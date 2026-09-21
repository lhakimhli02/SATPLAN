#!/usr/bin/env python3
"""
animate_ferry.py - Animate Ferry transport plan search and execution.

Left panel  : Planning graph growing horizon by horizon
Right panel : Two shores + body of water with a sliding ferry and cars

Usage:
    python animate_ferry.py -o domain.pddl -f problem.pddl [options]

Options:
    --steps N       Max horizons to try (default: 35)
    --interval N    ms per logical plan step (default: 1000)
    --save PATH     Save as .gif or .mp4
    --no-noop       Hide NOOP actions in graph panel
    --debug N       Debug level (default: 0)
"""
from __future__ import annotations
import sys, os, argparse

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import matplotlib.animation as manim
from matplotlib.gridspec import GridSpec

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from graphplan import PlanningGraph
from data_structures import CONNECTOR, NOOP
from visualize_graphplan import C_BG, render_layer

# ── Constants ─────────────────────────────────────────────────────────────────
N_SUB        = 6
SEARCH_MS    = 200
FRAME_MS     = 50

# Shore / water layout (fractions of axis width)
SHORE_L      = 0.00
MID_L        = 0.28
MID_R        = 0.72
SHORE_R      = 1.00

# Ferry position when docked at each shore
FERRY_CX     = {'left': 0.355, 'right': 0.645}
FERRY_W      = 0.17
FERRY_H      = 0.11
FERRY_Y      = 0.50   # y-centre of ferry

CAR_W        = 0.090
CAR_H        = 0.042
CAR_GAP      = 0.014

GOAL_COLOR   = '#27AE60'
BG_WATER     = '#5DADE2'
BG_SHORE     = '#F5CBA7'
FERRY_COLOR  = '#2C3E50'

CAR_PALETTE  = [
    '#E74C3C', '#3498DB', '#2ECC71', '#F39C12',
    '#9B59B6', '#1ABC9C', '#E67E22', '#34495E',
    '#C0392B', '#2980B9', '#27AE60', '#E67E22',
]


def _ease(t: float) -> float:
    return t * t * (3.0 - 2.0 * t)


# ── State ─────────────────────────────────────────────────────────────────────

class FerryState:
    __slots__ = ('ferry_loc', 'ferry_empty', 'car_at', 'car_on')

    def __init__(self):
        self.ferry_loc:   str            = 'left'
        self.ferry_empty: bool           = True
        self.car_at:      dict[str, str] = {}   # car → 'left' | 'right'
        self.car_on:      str | None     = None  # car currently on ferry

    def copy(self) -> 'FerryState':
        s = FerryState()
        s.ferry_loc   = self.ferry_loc
        s.ferry_empty = self.ferry_empty
        s.car_at      = dict(self.car_at)
        s.car_on      = self.car_on
        return s


def _parse_objects(graph: PlanningGraph) -> tuple[list[str], list[str]]:
    cars: set[str]      = set()
    locations: set[str] = set()
    for fact in graph.initial_facts:
        pred = fact[0].lower()
        args = [a.lower() for a in fact[1:]]
        if pred == 'at-ferry' and args:
            locations.add(args[0])
        elif pred == 'at' and len(args) == 2:
            cars.add(args[0])
            locations.add(args[1])
        elif pred == 'on' and args:
            cars.add(args[0])
    for goal in graph.the_goals:
        if goal[0].lower() == 'at' and len(goal) == 3:
            locations.add(goal[2].lower())
    return sorted(cars), sorted(locations)


def _parse_initial_state(graph: PlanningGraph) -> FerryState:
    s = FerryState()
    for fact in graph.initial_facts:
        pred = fact[0].lower()
        args = [a.lower() for a in fact[1:]]
        if pred == 'at-ferry' and args:
            s.ferry_loc = args[0]
        elif pred == 'empty':
            s.ferry_empty = True
        elif pred == 'at' and len(args) == 2:
            s.car_at[args[0]] = args[1]
        elif pred == 'on' and args:
            s.car_on      = args[0]
            s.ferry_empty = False
    return s


def _apply_action(s: FerryState, name: str) -> FerryState:
    if NOOP in name.lower():
        return s.copy()
    ns    = s.copy()
    parts = name.lower().split(CONNECTOR)
    atype = parts[0]
    args  = parts[1:]
    if atype == 'sail' and len(args) >= 2:
        ns.ferry_loc = args[1]
    elif atype == 'board' and len(args) >= 2:
        car = args[0]
        ns.car_at.pop(car, None)
        ns.car_on      = car
        ns.ferry_empty = False
    elif atype == 'debark' and len(args) >= 2:
        car, loc       = args[0], args[1]
        ns.car_on      = None
        ns.ferry_empty = True
        ns.car_at[car] = loc
    return ns



# ── Renderer ──────────────────────────────────────────────────────────────────

def _car_shore_positions(cars_on_shore: list[str], shore: str,
                         all_cars: list[str]) -> dict[str, tuple[float, float]]:
    """Compute (cx, cy) for cars stacked vertically on a shore."""
    n     = len(cars_on_shore)
    if shore == 'left':
        cx = (SHORE_L + MID_L) / 2
    else:
        cx = (MID_R + SHORE_R) / 2
    # Distribute from bottom to top, centred vertically
    total_h = n * CAR_H + max(n - 1, 0) * CAR_GAP
    y_start = FERRY_Y - total_h / 2
    return {car: (cx, y_start + i * (CAR_H + CAR_GAP) + CAR_H / 2)
            for i, car in enumerate(sorted(cars_on_shore))}


def render_ferry(ax, state: FerryState, ferry_cx: float,
                 cars: list[str], goal_cars: set[str], car_colors: dict,
                 step_num: int, total_steps: int, actions: list[str],
                 title_extra: str = '') -> None:
    ax.clear()
    ax.set_xlim(0, 1); ax.set_ylim(0, 1); ax.axis('off')

    # ── Background ────────────────────────────────────────────────────────
    # Water
    ax.add_patch(mpatches.FancyBboxPatch(
        (MID_L, 0.00), MID_R - MID_L, 1.00,
        boxstyle='square,pad=0', facecolor=BG_WATER, zorder=1))
    # Shores
    ax.add_patch(mpatches.FancyBboxPatch(
        (SHORE_L, 0.00), MID_L - SHORE_L, 1.00,
        boxstyle='square,pad=0', facecolor=BG_SHORE, zorder=1))
    ax.add_patch(mpatches.FancyBboxPatch(
        (MID_R, 0.00), SHORE_R - MID_R, 1.00,
        boxstyle='square,pad=0', facecolor=BG_SHORE, zorder=1))

    # Shore labels
    ax.text((SHORE_L + MID_L) / 2, 0.93, 'LEFT',
            ha='center', va='top', fontsize=10, fontweight='bold', color='#5D4037')
    ax.text((MID_R + SHORE_R) / 2, 0.93, 'RIGHT',
            ha='center', va='top', fontsize=10, fontweight='bold', color='#5D4037')

    # Wave lines (decorative)
    for wy in (0.35, 0.50, 0.65):
        for wx in (0.32, 0.42, 0.52, 0.62, 0.68):
            ax.plot([wx, wx + 0.04], [wy, wy + 0.012],
                    color='white', alpha=0.35, linewidth=1.2, zorder=2)

    # ── Ferry ─────────────────────────────────────────────────────────────
    ax.add_patch(mpatches.FancyBboxPatch(
        (ferry_cx - FERRY_W / 2, FERRY_Y - FERRY_H / 2), FERRY_W, FERRY_H,
        boxstyle='round,pad=0.005', facecolor=FERRY_COLOR,
        edgecolor='#ECF0F1', linewidth=2, zorder=5))
    ax.text(ferry_cx, FERRY_Y + FERRY_H / 2 + 0.025, 'FERRY',
            ha='center', va='bottom', fontsize=7, color='#ECF0F1',
            fontweight='bold', zorder=6)

    # Car on ferry
    if state.car_on:
        car  = state.car_on
        fc   = car_colors.get(car, '#999')
        ax.add_patch(mpatches.FancyBboxPatch(
            (ferry_cx - CAR_W / 2, FERRY_Y - CAR_H / 2), CAR_W, CAR_H,
            boxstyle='round,pad=0.003', facecolor=fc, edgecolor='#ECF0F1',
            linewidth=1.5, zorder=7))
        ax.text(ferry_cx, FERRY_Y, car.upper(), ha='center', va='center',
                fontsize=7, fontweight='bold', color='white', zorder=8)

    # ── Cars on shores ────────────────────────────────────────────────────
    left_cars  = [c for c, loc in state.car_at.items() if loc == 'left']
    right_cars = [c for c, loc in state.car_at.items() if loc == 'right']

    for shore, car_list in (('left', left_cars), ('right', right_cars)):
        positions = _car_shore_positions(car_list, shore, cars)
        for car, (cx, cy) in positions.items():
            arrived    = (shore == 'right')
            is_goal    = car in goal_cars and arrived
            ec         = GOAL_COLOR if is_goal else '#555555'
            lw         = 2.0 if is_goal else 0.8
            fc         = car_colors.get(car, '#999')
            ax.add_patch(mpatches.FancyBboxPatch(
                (cx - CAR_W / 2, cy - CAR_H / 2), CAR_W, CAR_H,
                boxstyle='round,pad=0.003', facecolor=fc,
                edgecolor=ec, linewidth=lw, zorder=4))
            ax.text(cx, cy, car.upper(), ha='center', va='center',
                    fontsize=6, fontweight='bold', color='white', zorder=5)

    # ── Status ────────────────────────────────────────────────────────────
    n_arrived = len(right_cars)
    n_total   = len(cars)
    ax.text(0.5, 0.97, f'Step {step_num} / {total_steps}  {title_extra}',
            ha='center', va='top', fontsize=9, fontweight='bold',
            color='#1B2631', transform=ax.transAxes)
    ax.text(0.5, 0.035, f'{n_arrived} / {n_total} cars arrived',
            ha='center', va='bottom', fontsize=8, color='#2C3E50',
            transform=ax.transAxes)
    if actions:
        label = ',  '.join(f'({a.replace(CONNECTOR, " ")})' for a in actions)
        ax.text(0.5, 0.93, 'Actions: ' + label, ha='center', va='top',
                fontsize=7, color='#2C3E50', transform=ax.transAxes)

    ax.legend(
        handles=[mpatches.Patch(facecolor='white', edgecolor=GOAL_COLOR,
                                linewidth=2.0, label='Goal: arrived')],
        loc='lower right', fontsize=7, framealpha=0.85)


# ── Sub-frame interpolation ───────────────────────────────────────────────────

def _ferry_subframes(state_start: FerryState, state_end: FerryState,
                     acts: list[str]) -> list[tuple[FerryState, float]]:
    """Return N_SUB (display_state, ferry_cx) pairs for one plan step."""
    is_sail   = any(a.lower().startswith('sail') for a in acts)
    cx_start  = FERRY_CX.get(state_start.ferry_loc, 0.5)
    cx_end    = FERRY_CX.get(state_end.ferry_loc,   0.5)

    result: list[tuple[FerryState, float]] = []
    for fi in range(N_SUB):
        t  = (fi + 1) / N_SUB
        if is_sail:
            # Smooth ferry slide; show end state (passengers board/debark instantly)
            cx = cx_start + (cx_end - cx_start) * _ease(t)
        else:
            # Non-sail: instant state change at midpoint
            cx = cx_end
        disp = state_end if (fi >= N_SUB // 2 or is_sail) else state_start
        result.append((disp, cx))
    return result


# ── Direct plan generation (no solver) ────────────────────────────────────────

def _generate_ferry_plan(initial: FerryState, all_goals: list) -> list[str]:
    """Build a valid sequential ferry plan from goal list without any planner."""
    car_goals: dict[str, str] = {}
    for g in all_goals:
        if g[0].lower() == 'at' and len(g) == 3:
            car_goals[g[1].lower()] = g[2].lower()

    state = initial.copy()
    plan: list[str] = []
    for car in sorted(car_goals):
        goal_loc  = car_goals[car]
        start_loc = state.car_at.get(car)
        if start_loc is None or start_loc == goal_loc:
            continue
        if state.ferry_loc != start_loc:
            plan.append(CONNECTOR.join(['sail', state.ferry_loc, start_loc]))
            state.ferry_loc = start_loc
        plan.append(CONNECTOR.join(['board', car, start_loc]))
        state.car_at.pop(car, None)
        state.car_on      = car
        state.ferry_empty = False
        plan.append(CONNECTOR.join(['sail', state.ferry_loc, goal_loc]))
        state.ferry_loc = goal_loc
        plan.append(CONNECTOR.join(['debark', car, goal_loc]))
        state.car_at[car] = goal_loc
        state.car_on      = None
        state.ferry_empty = True
    return plan


def _states_from_actions(initial: FerryState, actions: list[str]) -> list[tuple]:
    states = [(initial.copy(), [])]
    cur    = initial.copy()
    for act in actions:
        cur = _apply_action(cur, act)
        states.append((cur.copy(), [act]))
    return states


# ── Full search + animation builder ───────────────────────────────────────────

def run_full_search(domain_file: str, problem_file: str, max_steps: int, debug: int,
                    show_graph: bool = True):
    graph = PlanningGraph()
    graph.debug_flag = debug
    graph.load(domain_file, problem_file)
    graph.process_data()
    if show_graph:
        graph.create_graph(max_steps, auto_stop=False)
    initial   = _parse_initial_state(graph)
    cars, locs = _parse_objects(graph)
    all_goals = list(graph.the_goals)

    # Generate plan directly — graphplan backward chaining is too slow for
    # sequential ferry problems (UNSAT-proving at each horizon takes minutes)
    plan_actions = _generate_ferry_plan(initial, all_goals)
    plan_states  = _states_from_actions(initial, plan_actions)
    plan_horizon = len(plan_actions)

    if show_graph:
        # Show a few evenly-spaced search horizons before execution
        n_search   = min(3, plan_horizon - 1)
        step_size  = max(1, plan_horizon // (n_search + 1))
        search_hs  = list(range(step_size, plan_horizon, step_size))[:n_search]
        horizon_data: list = [(h, [(initial.copy(), [])], [], False) for h in search_hs]
        horizon_data.append((plan_horizon, plan_states, all_goals, True))
    else:
        horizon_data = [(plan_horizon, plan_states, all_goals, True)]

    return graph, plan_horizon, horizon_data, initial, cars, locs, all_goals


def build_animation(domain_file: str, problem_file: str, max_steps: int, debug: int,
                    show_noop: bool, max_facts: int, max_actions: int, interval: int,
                    show_graph: bool = True):
    print(f'Loading {domain_file} + {problem_file}')
    (graph, plan_horizon, horizon_data,
     initial, cars, locs, all_goals) = run_full_search(
        domain_file, problem_file, max_steps, debug, show_graph=show_graph)

    goal_cars   = {g[1].lower() for g in all_goals if g[0].lower() == 'at' and len(g) == 3}
    goal_names  = {CONNECTOR.join(g) for g in all_goals}
    car_colors  = {c: CAR_PALETTE[i % len(CAR_PALETTE)] for i, c in enumerate(cars)}
    num_layers  = len(graph.op_table)

    if plan_horizon < 0:
        print(f'No plan found within {max_steps} steps.')
    else:
        print(f'Plan found at horizon {plan_horizon}.')

    frame_ms        = max(20, interval // N_SUB)
    n_search_frames = max(1, SEARCH_MS // frame_ms)
    frames: list[dict] = []

    for h, plan_states, achieved, is_full in horizon_data:
        graph_layer = min(h - 1, num_layers - 1)
        n_goals     = len(all_goals)
        n_ach       = len(achieved)
        reachable_g = {
            CONNECTOR.join(g) for g in all_goals
            if h < len(graph.fact_table)
            and graph.fact_table[h].lookup(CONNECTOR.join(g)) is not None
        }

        if not is_full:
            final_state, _ = plan_states[-1]
            cx = FERRY_CX.get(final_state.ferry_loc, 0.5)
            frame = dict(
                graph_layer=graph_layer, state=final_state, ferry_cx=cx,
                step_num=len(plan_states) - 1, total_steps=len(plan_states) - 1,
                actions=[], title_extra=f'— {n_ach}/{n_goals} cars achievable',
                horizon=h, phase='search', reachable_goals=reachable_g,
            )
            for _ in range(n_search_frames):
                frames.append(frame)
        else:
            total_steps = len(plan_states) - 1
            for step_i in range(len(plan_states)):
                state, _ = plan_states[step_i]
                if step_i + 1 < len(plan_states):
                    next_state, acts = plan_states[step_i + 1]
                    subframes = _ferry_subframes(state, next_state, acts)
                    for sfi, (disp_state, cx) in enumerate(subframes):
                        frames.append(dict(
                            graph_layer=graph_layer, state=disp_state, ferry_cx=cx,
                            step_num=step_i, total_steps=total_steps,
                            actions=acts if sfi >= N_SUB // 2 else [],
                            title_extra=f'— {n_goals}/{n_goals} goals',
                            horizon=h, phase='execute', reachable_goals=reachable_g,
                        ))
                else:
                    cx = FERRY_CX.get(state.ferry_loc, 0.5)
                    fr = dict(
                        graph_layer=graph_layer, state=state, ferry_cx=cx,
                        step_num=step_i, total_steps=total_steps, actions=[],
                        title_extra='— Goal achieved!',
                        horizon=h, phase='execute', reachable_goals=reachable_g,
                    )
                    for _ in range(N_SUB):
                        frames.append(fr)

    print(f'Animation: {len(frames)} frames at {frame_ms} ms each '
          f'({len(frames) * frame_ms / 1000:.1f}s total, loops)')

    if show_graph:
        fig = plt.figure(figsize=(16, 6))
        fig.patch.set_facecolor(C_BG)
        gs = GridSpec(1, 2, figure=fig, left=0.01, right=0.99, top=0.91, bottom=0.06,
                      wspace=0.04, width_ratios=[2, 1])
        ax_graph = fig.add_subplot(gs[0])
        ax_ferry = fig.add_subplot(gs[1])
    else:
        fig = plt.figure(figsize=(9, 6))
        fig.patch.set_facecolor(C_BG)
        ax_graph = None
        ax_ferry = fig.add_subplot(111)

    def _suptitle(fr: dict) -> str:
        h = fr['horizon']
        if fr['phase'] == 'execute':
            return (f'Plan found at horizon {h}  —  '
                    f'Executing step {fr["step_num"]} / {fr["total_steps"]}')
        return f'Horizon {h}  —  Searching…  {fr["title_extra"]}'

    _last_rendered_layer = [-1]

    def update(fi: int):
        fr = frames[fi]
        t  = fr['graph_layer']
        rg = fr.get('reachable_goals', goal_names)
        # Only re-render planning graph when the layer actually changes
        if show_graph and t != _last_rendered_layer[0] and t < len(graph.op_table):
            render_layer(ax_graph, graph, t, rg, show_noop=show_noop,
                         max_facts=max_facts, max_actions=max_actions)
            _last_rendered_layer[0] = t
        render_ferry(ax_ferry, fr['state'], fr['ferry_cx'],
                     cars, goal_cars, car_colors,
                     fr['step_num'], fr['total_steps'],
                     fr['actions'], fr['title_extra'])
        fig.suptitle(_suptitle(fr), fontsize=12, fontweight='bold', color='#1B2631', y=0.97)
        fig.canvas.draw_idle()

    ani = manim.FuncAnimation(fig, update, frames=len(frames),
                               interval=frame_ms, repeat=True, blit=False)
    update(0)
    return fig, ani


# ── Entry point ───────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description='Animate Ferry transport')
    parser.add_argument('-o', '--domain',      required=True)
    parser.add_argument('-f', '--problem',     required=True)
    parser.add_argument('--steps',       type=int, default=35)
    parser.add_argument('--interval',    type=int, default=1000)
    parser.add_argument('--save',        default=None)
    parser.add_argument('--no-noop',     action='store_true')
    parser.add_argument('--max-facts',   type=int, default=45)
    parser.add_argument('--max-actions', type=int, default=60)
    parser.add_argument('--debug',       type=int, default=0)
    parser.add_argument('--no-graph',    action='store_true',
                        help='Hide the planning-graph panel; animate the '
                             'world-state execution only')
    args = parser.parse_args()

    _fig, ani = build_animation(
        domain_file=args.domain, problem_file=args.problem,
        max_steps=args.steps, debug=args.debug,
        show_noop=not args.no_noop,
        max_facts=args.max_facts, max_actions=args.max_actions,
        interval=args.interval,
        show_graph=not args.no_graph,
    )
    if args.save:
        print(f'Saving to {args.save} ...')
        ext    = os.path.splitext(args.save)[1].lower()
        fps    = max(1, N_SUB * 1000 // max(20, args.interval))
        writer = (manim.PillowWriter(fps=fps) if ext == '.gif'
                  else manim.FFMpegWriter(fps=fps, bitrate=1800))
        ani.save(args.save, writer=writer, dpi=72)
        print('Saved.')
        plt.close('all')
    else:
        print('Close the window to exit.')
        plt.show()


if __name__ == '__main__':
    main()
