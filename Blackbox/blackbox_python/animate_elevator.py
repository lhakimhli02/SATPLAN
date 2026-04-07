#!/usr/bin/env python3
"""
animate_elevator.py - Animate elevator plan search and execution.

Shows two panels side-by-side:
  Left  : Planning graph at the current horizon layer
  Right : Elevator building with smoothly moving car(s) and passengers

Animation sequence
------------------
For each horizon h = 1, 2, …, T_final:
  • Show the planning graph at layer h-1
  • If no full plan yet: show the best partial plan state
  • If a full plan IS found at horizon h: animate step-by-step with smooth
    elevator movement, then stop

Usage
-----
    python animate_elevator.py -o domain.pddl -f problem.pddl [options]

Options
-------
  --steps N        Max horizons to try (default: 20)
  --interval N     Milliseconds per logical plan step (default: 1200)
  --save PATH      Save animation as MP4 or GIF
  --no-noop        Hide NOOP actions in planning-graph panel
  --max-facts N    Max fact nodes per column (default: 45)
  --max-actions N  Max action nodes per column (default: 60)
  --debug N        Debug level (default: 0)
"""

from __future__ import annotations
import sys, os, argparse, itertools

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import matplotlib.animation as manim
from matplotlib.gridspec import GridSpec

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from graphplan import PlanningGraph
from planner import Planner
from data_structures import CONNECTOR, NOOP, SolverSpec, Graphplan_Solver, Anysat, Sat
from visualize_graphplan import C_BG, render_layer


# ── Layout constants ──────────────────────────────────────────────────────────
N_SUB       = 12    # sub-frames per execution step
SEARCH_MS   = 500   # ms each search-phase frame is displayed
FRAME_MS    = 50    # ms per rendered frame → 20 fps

Y_BOTTOM    = 0.08  # y of ground floor centre
Y_TOP       = 0.88  # y of top floor centre

BG_ELEV     = '#F0F4F8'
SHAFT_COL   = '#90A4AE'
CAR_COL     = '#455A64'
FLOOR_LINE  = '#B0BEC5'
WALL_COL    = '#78909C'
GOAL_COLOR  = '#27AE60'

PASSENGER_PALETTE = [
    '#E74C3C', '#3498DB', '#2ECC71', '#F39C12',
    '#9B59B6', '#1ABC9C', '#E67E22', '#34495E',
]


# ── Elevator state ────────────────────────────────────────────────────────────

class ElevatorState:
    def __init__(self):
        self.lift_floor:      dict[str, str] = {}  # lift  → floor name
        self.passenger_floor: dict[str, str] = {}  # pass  → floor name
        self.boarded:         dict[str, str] = {}  # pass  → lift name

    def copy(self) -> 'ElevatorState':
        s = ElevatorState()
        s.lift_floor      = dict(self.lift_floor)
        s.passenger_floor = dict(self.passenger_floor)
        s.boarded         = dict(self.boarded)
        return s


# ── Parsing helpers ───────────────────────────────────────────────────────────

def _parse_objects(graph: PlanningGraph) -> tuple[list[str], list[str]]:
    """Return (sorted lifts, sorted passengers) from initial facts."""
    lifts: set[str] = set()
    passengers: set[str] = set()
    for fact in graph.initial_facts:
        pred = fact[0].lower()
        args = [a.lower() for a in fact[1:]]
        if pred == 'lift-at' and len(args) == 2:
            lifts.add(args[0])
        elif pred == 'passenger-at' and len(args) == 2:
            passengers.add(args[0])
        elif pred == 'boarded' and len(args) == 2:
            passengers.add(args[0])
            lifts.add(args[1])
    return sorted(lifts), sorted(passengers)


def _parse_floor_order(graph: PlanningGraph) -> list[str]:
    """Return floor names sorted bottom-to-top using 'above' facts.

    Our simplified domain uses above(lower, upper), i.e. above(f0, f1)
    means f1 is one level above f0.
    """
    above_pairs: list[tuple[str, str]] = []
    all_floors: set[str] = set()
    for fact in graph.initial_facts:
        if fact[0].lower() == 'above' and len(fact) == 3:
            lo, hi = fact[1].lower(), fact[2].lower()
            above_pairs.append((lo, hi))
            all_floors.update([lo, hi])

    if not all_floors:
        return []

    has_predecessor: set[str] = {hi for _, hi in above_pairs}
    successors: dict[str, list[str]] = {f: [] for f in all_floors}
    for lo, hi in above_pairs:
        successors[lo].append(hi)

    # Start from floors with no predecessor (ground floors)
    bottoms = sorted(f for f in all_floors if f not in has_predecessor)
    current = bottoms[0] if bottoms else sorted(all_floors)[0]

    ordered: list[str] = []
    visited: set[str] = set()
    while current and current not in visited:
        ordered.append(current)
        visited.add(current)
        nexts = [h for h in successors.get(current, []) if h not in visited]
        current = sorted(nexts)[0] if nexts else None

    for f in sorted(all_floors):
        if f not in visited:
            ordered.append(f)
    return ordered


def _parse_initial_state(graph: PlanningGraph) -> ElevatorState:
    s = ElevatorState()
    for fact in graph.initial_facts:
        pred = fact[0].lower()
        args = [a.lower() for a in fact[1:]]
        if pred == 'lift-at' and len(args) == 2:
            s.lift_floor[args[0]] = args[1]
        elif pred == 'passenger-at' and len(args) == 2:
            s.passenger_floor[args[0]] = args[1]
        elif pred == 'boarded' and len(args) == 2:
            s.boarded[args[0]] = args[1]
    return s


# ── Action simulation ─────────────────────────────────────────────────────────

def _parse_action(name: str) -> tuple[str, list[str]]:
    n = name.lower()
    for prefix in ('move-up', 'move-down', 'board', 'leave'):
        if n.startswith(prefix + CONNECTOR):
            rest = n[len(prefix) + len(CONNECTOR):]
            return prefix, rest.split(CONNECTOR)
    parts = n.split(CONNECTOR)
    return parts[0], parts[1:]


def _apply_action(s: ElevatorState, action_name: str) -> ElevatorState:
    if NOOP in action_name.lower():
        return s.copy()
    ns = s.copy()
    atype, args = _parse_action(action_name)
    if atype in ('move-up', 'move-down') and len(args) >= 3:
        lift, _f1, f2 = args[0], args[1], args[2]
        ns.lift_floor[lift] = f2
    elif atype == 'board' and len(args) >= 3:
        p, lift, _f = args[0], args[1], args[2]
        ns.passenger_floor.pop(p, None)
        ns.boarded[p] = lift
    elif atype == 'leave' and len(args) >= 3:
        p, _lift, f = args[0], args[1], args[2]
        ns.boarded.pop(p, None)
        ns.passenger_floor[p] = f  # floor is encoded in the action args
    return ns


def _extract_plan_states(graph: PlanningGraph, maxtime: int,
                         initial: ElevatorState) -> list[tuple[ElevatorState, list[str]]]:
    """Simulate the plan and return (state_before_step, actions_at_step)."""
    states = [(initial.copy(), [])]
    cur = initial.copy()
    for t in range(maxtime):
        acts = [op.name for op in graph.op_table[t] if op.used and not op.is_noop]
        for a in acts:
            cur = _apply_action(cur, a)
        states.append((cur.copy(), acts))
    return states


def _pretty_action(name: str) -> str:
    atype, args = _parse_action(name)
    return f'({atype} {" ".join(a.upper() for a in args)})'


# ── Building renderer ─────────────────────────────────────────────────────────

def _floor_y(floor_idx: int, n_floors: int) -> float:
    """Y coordinate of floor centre; floor 0 is the bottom."""
    if n_floors <= 1:
        return (Y_BOTTOM + Y_TOP) / 2
    return Y_BOTTOM + floor_idx * (Y_TOP - Y_BOTTOM) / (n_floors - 1)


def render_elevator(
        ax,
        state:            ElevatorState,
        lift_y:           dict[str, float],   # lift → current animated y
        floor_order:      list[str],
        lifts:            list[str],
        passengers:       list[str],
        passenger_colors: dict[str, str],
        goal_passengers:  set[str],
        step_num:         int,
        total_steps:      int,
        actions:          list[str],
        title_extra:      str = '',
):
    ax.clear()
    ax.set_facecolor(BG_ELEV)
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.axis('off')

    n_floors  = len(floor_order)
    floor_idx = {f: i for i, f in enumerate(floor_order)}
    floor_h   = (Y_TOP - Y_BOTTOM) / max(n_floors - 1, 1) if n_floors > 1 else 0.4

    # Geometry: shaft band on the left, waiting area on the right
    n_lifts      = max(len(lifts), 1)
    shaft_left   = 0.10
    shaft_right  = shaft_left + 0.14 * n_lifts
    shaft_w      = (shaft_right - shaft_left) / n_lifts
    wait_left    = shaft_right + 0.04
    wait_right   = 0.97

    # ── Building outline ─────────────────────────────────────────────────
    ax.add_patch(mpatches.FancyBboxPatch(
        (shaft_left - 0.01, Y_BOTTOM - floor_h * 0.5),
        wait_right - shaft_left + 0.02,
        Y_TOP - Y_BOTTOM + floor_h,
        boxstyle='round,pad=0.005',
        facecolor='none', edgecolor=WALL_COL, linewidth=2, zorder=1,
    ))

    # ── Floors ───────────────────────────────────────────────────────────
    for fi, floor in enumerate(floor_order):
        fy = _floor_y(fi, n_floors)
        # Floor separator line (below each floor except ground)
        line_y = fy - floor_h * 0.5
        ax.plot([shaft_left - 0.01, wait_right],
                [line_y, line_y],
                color=FLOOR_LINE, linewidth=0.8, zorder=2)
        # Floor label on the left margin
        ax.text(shaft_left - 0.025, fy,
                floor.upper(),
                ha='right', va='center', fontsize=8,
                fontweight='bold', color='#37474F')

    # ── Shaft backgrounds ─────────────────────────────────────────────────
    for li, lift in enumerate(lifts):
        sx = shaft_left + li * shaft_w
        ax.add_patch(mpatches.FancyBboxPatch(
            (sx + 0.004, Y_BOTTOM - floor_h * 0.5 + 0.005),
            shaft_w - 0.008,
            Y_TOP - Y_BOTTOM + floor_h - 0.010,
            boxstyle='square,pad=0',
            facecolor='#CFD8DC', edgecolor=SHAFT_COL, linewidth=1, zorder=2,
        ))

    # ── Elevator cars ─────────────────────────────────────────────────────
    car_h = floor_h * 0.65
    for li, lift in enumerate(lifts):
        sx = shaft_left + li * shaft_w
        cx = sx + shaft_w / 2
        cy = lift_y.get(lift, _floor_y(
            floor_idx.get(state.lift_floor.get(lift, floor_order[0]), 0), n_floors))
        car_w = shaft_w * 0.78

        ax.add_patch(mpatches.FancyBboxPatch(
            (cx - car_w / 2, cy - car_h / 2), car_w, car_h,
            boxstyle='round,pad=0.003',
            facecolor=CAR_COL, edgecolor='#1C313A', linewidth=1.5, zorder=5,
        ))
        ax.text(cx, cy + car_h * 0.28, lift.upper(),
                ha='center', va='center', fontsize=5,
                color='#CFD8DC', fontweight='bold', zorder=6)

        # Boarded passengers inside the car
        boarded_here = sorted(p for p, l in state.boarded.items() if l == lift)
        n_b = len(boarded_here)
        for bi, p in enumerate(boarded_here):
            r  = min(0.016, car_w * 0.25)
            bx = cx + (bi - (n_b - 1) / 2) * (car_w / max(n_b + 1, 2))
            by = cy - car_h * 0.05
            circle = plt.Circle((bx, by), r,
                                 color=passenger_colors.get(p, '#999'),
                                 zorder=7)
            ax.add_patch(circle)
            ax.text(bx, by, p[1:],  # strip leading 'p'
                    ha='center', va='center', fontsize=5,
                    fontweight='bold', color='white', zorder=8)

    # ── Waiting passengers ────────────────────────────────────────────────
    by_floor: dict[str, list[str]] = {f: [] for f in floor_order}
    for p, f in state.passenger_floor.items():
        if f in by_floor:
            by_floor[f].append(p)

    wait_w = wait_right - wait_left
    for fi, floor in enumerate(floor_order):
        fy    = _floor_y(fi, n_floors)
        plist = sorted(by_floor.get(floor, []))
        n_p   = len(plist)
        for pi, p in enumerate(plist):
            r  = 0.022
            px = wait_left + (pi + 0.5) * wait_w / max(n_p, 4)
            py = fy
            is_goal = p in goal_passengers
            circle = plt.Circle((px, py), r,
                                 color=passenger_colors.get(p, '#999'),
                                 zorder=4)
            ax.add_patch(circle)
            if is_goal:
                outline = plt.Circle((px, py), r,
                                     color=GOAL_COLOR, fill=False,
                                     linewidth=2.5, zorder=5)
                ax.add_patch(outline)
            ax.text(px, py, p[1:],
                    ha='center', va='center', fontsize=7,
                    fontweight='bold', color='white', zorder=6)

    # ── Status text ───────────────────────────────────────────────────────
    ax.text(0.5, 0.97,
            f'Step {step_num} / {total_steps}  {title_extra}',
            ha='center', va='top', fontsize=9, fontweight='bold',
            color='#1B2631', transform=ax.transAxes)

    if actions:
        label = '   '.join(_pretty_action(a) for a in actions)
        ax.text(0.5, 0.93,
                'Actions: ' + label,
                ha='center', va='top', fontsize=7, color='#2C3E50',
                transform=ax.transAxes)
    else:
        ax.text(0.5, 0.93, '(initial state)',
                ha='center', va='top', fontsize=7.5,
                color='#7F8C8D', transform=ax.transAxes)

    goal_patch = mpatches.Patch(facecolor='white', edgecolor=GOAL_COLOR,
                                linewidth=2.0, label='Goal passenger')
    ax.legend(handles=[goal_patch], loc='lower right', fontsize=7, framealpha=0.85)


# ── Smooth sub-frame interpolation ────────────────────────────────────────────

def _ease(t: float) -> float:
    return t * t * (3.0 - 2.0 * t)


def _lift_subframes(
        state_start: ElevatorState,
        state_end:   ElevatorState,
        floor_order: list[str],
        lifts:       list[str],
) -> list[dict[str, float]]:
    """Return N_SUB dicts mapping lift → animated y position."""
    n_floors  = len(floor_order)
    floor_idx = {f: i for i, f in enumerate(floor_order)}

    # Start / end y for each lift
    y_start = {
        lift: _floor_y(floor_idx.get(state_start.lift_floor.get(lift, floor_order[0]), 0),
                       n_floors)
        for lift in lifts
    }
    y_end = {
        lift: _floor_y(floor_idx.get(state_end.lift_floor.get(lift, floor_order[0]), 0),
                       n_floors)
        for lift in lifts
    }

    result: list[dict[str, float]] = []
    for fi in range(N_SUB):
        t  = (fi + 1) / N_SUB
        et = _ease(t)
        frame_y = {lift: y_start[lift] + (y_end[lift] - y_start[lift]) * et
                   for lift in lifts}
        result.append(frame_y)
    return result


# ── Partial plan search ───────────────────────────────────────────────────────

def find_best_partial_plan(
        graph:     PlanningGraph,
        planner:   Planner,
        all_goals: list,
        h:         int,
        initial:   ElevatorState,
        max_calls: int = 150,
) -> tuple[list[tuple[ElevatorState, list[str]]], list]:
    original_goals = list(graph.the_goals)
    best_states: list[tuple[ElevatorState, list[str]]] = [(initial, [])]
    best_goals:  list = []

    if h < len(graph.fact_table):
        reachable_idx = [
            i for i, g in enumerate(all_goals)
            if graph.fact_table[h].lookup(CONNECTOR.join(g)) is not None
        ]
    else:
        reachable_idx = []

    if not reachable_idx:
        graph.the_goals = original_goals
        return best_states, best_goals

    calls = 0
    for size in range(len(reachable_idx), 0, -1):
        found = False
        for indices in itertools.combinations(reachable_idx, size):
            graph.the_goals = [all_goals[i] for i in indices]
            if not graph.can_stop(h):
                continue
            if calls >= max_calls:
                break
            calls += 1
            if planner.do_plan(h) == Sat:
                best_states = _extract_plan_states(graph, h, initial)
                best_goals  = list(graph.the_goals)
                found = True
                break
        if found or calls >= max_calls:
            break

    graph.the_goals = original_goals
    return best_states, best_goals


# ── Planning search ───────────────────────────────────────────────────────────

def run_full_search(domain_file: str, problem_file: str,
                    max_steps: int, debug: int):
    graph = PlanningGraph()
    graph.debug_flag = debug
    graph.load(domain_file, problem_file)
    graph.process_data()
    graph.create_graph(max_steps, auto_stop=False)

    lifts, passengers = _parse_objects(graph)
    floor_order       = _parse_floor_order(graph)
    initial           = _parse_initial_state(graph)
    all_goals         = list(graph.the_goals)

    planner = Planner(
        graph=graph,
        solver_specs=[SolverSpec(solver_name='cadical',
                                 solver_type=Anysat)],
        debug=debug, noopt=True, do_justify=False,
    )

    horizon_data = []
    plan_horizon = -1
    for h in range(1, max_steps + 1):
        if h >= len(graph.fact_table):
            break
        states, achieved = find_best_partial_plan(
            graph, planner, all_goals, h, initial)
        is_full = len(achieved) == len(all_goals)
        horizon_data.append((h, states, achieved, is_full))
        if is_full:
            plan_horizon = h
            break

    return (graph, plan_horizon, horizon_data,
            initial, lifts, passengers, floor_order, all_goals)


# ── Animation builder ─────────────────────────────────────────────────────────

def build_animation(domain_file: str, problem_file: str,
                    max_steps: int, debug: int,
                    show_noop: bool, max_facts: int, max_actions: int,
                    interval: int):
    print(f'Loading {domain_file} + {problem_file}')
    (graph, plan_horizon, horizon_data,
     initial, lifts, passengers, floor_order, all_goals) = run_full_search(
        domain_file, problem_file, max_steps, debug)

    n_floors        = len(floor_order)
    floor_idx_map   = {f: i for i, f in enumerate(floor_order)}
    num_layers      = len(graph.op_table)
    goal_names_raw  = {CONNECTOR.join(g) for g in all_goals}

    if plan_horizon < 0:
        print(f'No plan found within {max_steps} steps.')
    else:
        print(f'Plan found at horizon {plan_horizon}')

    passenger_colors = {p: PASSENGER_PALETTE[i % len(PASSENGER_PALETTE)]
                        for i, p in enumerate(passengers)}
    goal_passengers  = {g[1].lower() for g in all_goals
                        if g[0].lower() == 'passenger-at' and len(g) >= 2}

    def _static_lift_y(state: ElevatorState) -> dict[str, float]:
        return {lift: _floor_y(floor_idx_map.get(state.lift_floor.get(lift, floor_order[0]), 0),
                               n_floors)
                for lift in lifts}

    # ── Build frame list ──────────────────────────────────────────────────
    frames: list[dict] = []
    n_search_frames = max(1, SEARCH_MS // FRAME_MS)

    for h, plan_states, achieved, is_full in horizon_data:
        graph_layer = min(h - 1, num_layers - 1)
        n_goals     = len(all_goals)
        n_achieved  = len(achieved)
        reachable_g = {
            CONNECTOR.join(g) for g in all_goals
            if h < len(graph.fact_table)
               and graph.fact_table[h].lookup(CONNECTOR.join(g)) is not None
        }

        if not is_full:
            final_state, _ = plan_states[-1]
            frame = dict(
                graph_layer    = graph_layer,
                state          = final_state,
                lift_y         = _static_lift_y(final_state),
                step_num       = len(plan_states) - 1,
                total_steps    = len(plan_states) - 1,
                actions        = [],
                title_extra    = (f'— {n_achieved}/{n_goals} goals achievable'
                                  if n_achieved else '— searching…'),
                horizon        = h,
                phase          = 'search',
                reachable_goals= reachable_g,
            )
            for _ in range(n_search_frames):
                frames.append(frame)

        else:
            total_steps = len(plan_states) - 1
            for step_i in range(len(plan_states)):
                cur_state, _ = plan_states[step_i]

                if step_i + 1 < len(plan_states):
                    next_state, acts = plan_states[step_i + 1]
                    sub_ys = _lift_subframes(cur_state, next_state, floor_order, lifts)

                    for fi, sub_y in enumerate(sub_ys):
                        # Show next_state for passengers from the first sub-frame:
                        # board → passenger boards before elevator moves away
                        # leave → passenger appears at floor while elevator departs
                        disp_state = next_state
                        sub_acts   = acts if fi >= N_SUB // 2 else []
                        frames.append(dict(
                            graph_layer    = graph_layer,
                            state          = disp_state,
                            lift_y         = sub_y,
                            step_num       = step_i,
                            total_steps    = total_steps,
                            actions        = sub_acts,
                            title_extra    = f'— {n_goals}/{n_goals} goals',
                            horizon        = h,
                            phase          = 'execute',
                            reachable_goals= reachable_g,
                        ))
                else:
                    # Final state — hold for N_SUB ticks
                    frame = dict(
                        graph_layer    = graph_layer,
                        state          = cur_state,
                        lift_y         = _static_lift_y(cur_state),
                        step_num       = step_i,
                        total_steps    = total_steps,
                        actions        = [],
                        title_extra    = '— Goal achieved!',
                        horizon        = h,
                        phase          = 'execute',
                        reachable_goals= reachable_g,
                    )
                    for _ in range(N_SUB):
                        frames.append(frame)

    print(f'Animation: {len(frames)} frames at {FRAME_MS} ms each '
          f'({len(frames) * FRAME_MS / 1000:.1f}s total, loops)')

    # ── Figure setup ──────────────────────────────────────────────────────
    fig = plt.figure(figsize=(20, 9))
    fig.patch.set_facecolor(C_BG)
    gs = GridSpec(1, 2, figure=fig,
                  left=0.01, right=0.99, top=0.91, bottom=0.06,
                  wspace=0.04, width_ratios=[2, 1])
    ax_graph = fig.add_subplot(gs[0])
    ax_elev  = fig.add_subplot(gs[1])

    def _suptitle(fr: dict) -> str:
        h = fr['horizon']
        if fr['phase'] == 'execute':
            s, t = fr['step_num'], fr['total_steps']
            return f'Plan found at horizon {h}  —  Executing step {s} / {t}'
        return f'Horizon {h}  —  Searching…  {fr["title_extra"]}'

    def update(frame_idx: int):
        fr = frames[frame_idx]
        t  = fr['graph_layer']
        reachable_g = fr.get('reachable_goals', goal_names_raw)
        if t < len(graph.op_table):
            render_layer(ax_graph, graph, t, reachable_g,
                         show_noop=show_noop,
                         max_facts=max_facts, max_actions=max_actions)
        render_elevator(
            ax_elev,
            state            = fr['state'],
            lift_y           = fr['lift_y'],
            floor_order      = floor_order,
            lifts            = lifts,
            passengers       = passengers,
            passenger_colors = passenger_colors,
            goal_passengers  = goal_passengers,
            step_num         = fr['step_num'],
            total_steps      = fr['total_steps'],
            actions          = fr['actions'],
            title_extra      = fr['title_extra'],
        )
        fig.suptitle(_suptitle(fr), fontsize=12, fontweight='bold',
                     color='#1B2631', y=0.97)
        fig.canvas.draw_idle()

    ani = manim.FuncAnimation(
        fig, update,
        frames=len(frames),
        interval=FRAME_MS,
        repeat=True, blit=False,
    )
    update(0)
    return fig, ani


# ── Entry point ───────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description='Animate elevator plan search and execution',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument('-o', '--domain',     required=True)
    parser.add_argument('-f', '--problem',    required=True)
    parser.add_argument('--steps',       type=int, default=20,
                        help='Max horizons to try (default: 20)')
    parser.add_argument('--interval',    type=int, default=1200,
                        help='Ms per logical plan step (default: 1200)')
    parser.add_argument('--save',        default=None,
                        help='Save as MP4 or GIF')
    parser.add_argument('--no-noop',     action='store_true')
    parser.add_argument('--max-facts',   type=int, default=45)
    parser.add_argument('--max-actions', type=int, default=60)
    parser.add_argument('--debug',       type=int, default=0)
    args = parser.parse_args()

    _fig, ani = build_animation(
        domain_file  = args.domain,
        problem_file = args.problem,
        max_steps    = args.steps,
        debug        = args.debug,
        show_noop    = not args.no_noop,
        max_facts    = args.max_facts,
        max_actions  = args.max_actions,
        interval     = args.interval,
    )

    if args.save:
        print(f'Saving to {args.save} …')
        ext = os.path.splitext(args.save)[1].lower()
        fps = max(1, 1000 // FRAME_MS)
        writer = (manim.PillowWriter(fps=fps) if ext == '.gif'
                  else manim.FFMpegWriter(fps=fps, bitrate=1800))
        ani.save(args.save, writer=writer, dpi=120)
        print('Saved.')
        plt.close('all')
    else:
        print('Close the window to exit.')
        plt.show()


if __name__ == '__main__':
    main()
