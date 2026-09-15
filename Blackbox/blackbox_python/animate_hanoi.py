#!/usr/bin/env python3
"""
animate_hanoi.py - Animate Towers of Hanoi plan search and execution.

Left panel  : Planning graph growing horizon by horizon
Right panel : Three pegs with discs (lift → slide → lower)

Usage:
    python animate_hanoi.py -o domain.pddl -f problem.pddl [options]

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
N_SUB      = 8
SEARCH_MS  = 200
FRAME_MS   = 50
ARM_Y      = 0.83
BASE_Y     = 0.13
DISC_H     = 0.065
DISC_GAP   = 0.006
PEG_W      = 0.018
PEG_TOP    = 0.87
WIDTH_MAX  = 0.30
WIDTH_MIN  = 0.09
BG_HANOI   = '#FAFAFA'
GOAL_COLOR = '#27AE60'

DISC_PALETTE = [
    '#E74C3C', '#3498DB', '#2ECC71', '#F39C12',
    '#9B59B6', '#1ABC9C', '#E67E22', '#34495E',
]


def _ease(t: float) -> float:
    return t * t * (3.0 - 2.0 * t)


# ── State ─────────────────────────────────────────────────────────────────────

class HanoiState:
    __slots__ = ('disc_on', 'clear')

    def __init__(self):
        self.disc_on: dict[str, str] = {}
        self.clear:   set[str]       = set()

    def copy(self) -> 'HanoiState':
        s = HanoiState()
        s.disc_on = dict(self.disc_on)
        s.clear   = set(self.clear)
        return s


def _parse_objects(graph: PlanningGraph) -> tuple[list[str], list[str]]:
    disc_set: set[str] = set()
    for fact in graph.initial_facts:
        if fact[0].lower() == 'on' and len(fact) == 3:
            disc_set.add(fact[1].lower())
    all_obj = {a.lower() for f in graph.initial_facts for a in f[1:]}
    peg_set = all_obj - disc_set
    return sorted(disc_set), sorted(peg_set)


def _initial_tower_order(graph: PlanningGraph) -> list[str]:
    """Discs sorted largest-first (= bottom of initial tower first)."""
    on_map   = {f[1].lower(): f[2].lower() for f in graph.initial_facts
                if f[0].lower() == 'on' and len(f) == 3}
    disc_set = set(on_map.keys())
    peg_set  = set(on_map.values()) - disc_set
    order: list[str] = []
    for peg in sorted(peg_set):
        cur = next((d for d, s in on_map.items() if s == peg), None)
        while cur is not None:
            order.append(cur)
            cur = next((d for d, s in on_map.items() if s == cur), None)
        if order:
            break
    for d in sorted(disc_set):
        if d not in order:
            order.append(d)
    return order   # order[0] = largest, order[-1] = smallest


def _parse_initial_state(graph: PlanningGraph) -> HanoiState:
    s = HanoiState()
    for fact in graph.initial_facts:
        pred = fact[0].lower()
        args = [a.lower() for a in fact[1:]]
        if pred == 'on'    and len(args) == 2: s.disc_on[args[0]] = args[1]
        elif pred == 'clear' and len(args) == 1: s.clear.add(args[0])
    return s


def _apply_action(s: HanoiState, name: str) -> HanoiState:
    if NOOP in name.lower():
        return s.copy()
    ns    = s.copy()
    parts = name.lower().split(CONNECTOR)
    if parts[0] == 'move' and len(parts) >= 4:
        disc, from_, to = parts[1], parts[2], parts[3]
        ns.disc_on[disc] = to
        ns.clear.discard(to)
        ns.clear.add(from_)
    return ns



# ── Geometry ──────────────────────────────────────────────────────────────────

def _peg_xs(pegs: list[str]) -> dict[str, float]:
    n  = len(pegs)
    xs = [0.22, 0.50, 0.78] if n == 3 else [0.1 + i * 0.8 / max(n - 1, 1) for i in range(n)]
    return {p: xs[i] for i, p in enumerate(sorted(pegs))}


def _disc_widths(disc_order: list[str]) -> dict[str, float]:
    n = len(disc_order)
    result: dict[str, float] = {}
    for i, d in enumerate(disc_order):
        t = i / max(n - 1, 1)           # 0 = largest, 1 = smallest
        result[d] = WIDTH_MAX * (1.0 - t) + WIDTH_MIN * t
    return result


def _build_peg_stack(state: HanoiState, discs: list[str], peg: str) -> list[str]:
    bottom = next((d for d in discs if state.disc_on.get(d) == peg), None)
    if bottom is None:
        return []
    stack, cur = [bottom], bottom
    while True:
        above = next((d for d in discs if state.disc_on.get(d) == cur), None)
        if above is None:
            break
        stack.append(above)
        cur = above
    return stack  # bottom → top


def state_to_positions(state: HanoiState, discs: list[str], pegs: list[str],
                       peg_x: dict[str, float]) -> dict[str, tuple[float, float]]:
    pos: dict[str, tuple[float, float]] = {}
    for peg in pegs:
        cx = peg_x[peg]
        for height, disc in enumerate(_build_peg_stack(state, discs, peg)):
            cy = BASE_Y + DISC_H / 2 + height * (DISC_H + DISC_GAP)
            pos[disc] = (cx, cy)
    return pos


# ── Sub-frame interpolation ───────────────────────────────────────────────────

def _step_subframes(pos_start: dict, pos_end: dict,
                    discs: list[str]) -> list[tuple[dict, str | None]]:
    moving = [d for d in discs if pos_start.get(d) != pos_end.get(d)]
    if not moving:
        return [(dict(pos_start), None)] * N_SUB
    mb = moving[0]
    sx, sy = pos_start[mb]
    ex, ey = pos_end[mb]
    # 3 phases: lift  slide  lower
    phases = [((sx, sy), (sx, ARM_Y)), ((sx, ARM_Y), (ex, ARM_Y)), ((ex, ARM_Y), (ex, ey))]
    n_ph   = len(phases)
    base_n = N_SUB // n_ph
    rem    = N_SUB - base_n * n_ph
    result: list[tuple[dict, str | None]] = []
    for pi, ((x0, y0), (x1, y1)) in enumerate(phases):
        nf = base_n + (rem if pi == n_ph - 1 else 0)
        for fi in range(nf):
            t  = (fi + 1) / nf
            et = _ease(t)
            p  = dict(pos_start)
            p[mb] = (x0 + (x1 - x0) * et, y0 + (y1 - y0) * et)
            result.append((p, mb))
    return result


# ── Renderer ──────────────────────────────────────────────────────────────────

def render_hanoi(ax, positions: dict, discs: list[str], pegs: list[str],
                 peg_x: dict, dwidths: dict, disc_colors: dict,
                 goal_set: set[str], step_num: int, total_steps: int,
                 actions: list[str], title_extra: str = '') -> None:
    ax.clear()
    ax.set_facecolor(BG_HANOI)
    ax.set_xlim(0, 1); ax.set_ylim(0, 1); ax.axis('off')

    # Platform
    ax.add_patch(mpatches.FancyBboxPatch((0.04, BASE_Y - 0.025), 0.92, 0.025,
        boxstyle='round,pad=0.002', facecolor='#A1887F',
        edgecolor='#795548', linewidth=1.5, zorder=2))

    # Peg poles + labels
    for peg in pegs:
        cx = peg_x[peg]
        ax.add_patch(mpatches.FancyBboxPatch(
            (cx - PEG_W / 2, BASE_Y), PEG_W, PEG_TOP - BASE_Y,
            boxstyle='square,pad=0', facecolor='#90A4AE',
            edgecolor='#607D8B', linewidth=1, zorder=3))
        ax.text(cx, BASE_Y - 0.055, peg.upper(),
                ha='center', va='top', fontsize=9, fontweight='bold', color='#37474F')

    # Discs
    for disc in discs:
        if disc not in positions:
            continue
        cx, cy = positions[disc]
        w  = dwidths.get(disc, 0.15)
        fc = disc_colors.get(disc, '#999')
        is_goal = disc in goal_set
        ax.add_patch(mpatches.FancyBboxPatch(
            (cx - w / 2, cy - DISC_H / 2), w, DISC_H,
            boxstyle='round,pad=0.003', facecolor=fc,
            edgecolor=GOAL_COLOR if is_goal else '#555555',
            linewidth=2.5 if is_goal else 1.0, zorder=4))
        ax.text(cx, cy, disc.upper(), ha='center', va='center',
                fontsize=8, fontweight='bold', color='white', zorder=5)

    # Status
    ax.text(0.5, 0.97, f'Step {step_num} / {total_steps}  {title_extra}',
            ha='center', va='top', fontsize=9, fontweight='bold',
            color='#1B2631', transform=ax.transAxes)
    if actions:
        label = ',  '.join(f'({a.replace(CONNECTOR, " ")})' for a in actions)
        ax.text(0.5, 0.93, 'Actions: ' + label, ha='center', va='top',
                fontsize=7.5, color='#2C3E50', transform=ax.transAxes)
    else:
        ax.text(0.5, 0.93, '(initial state)', ha='center', va='top',
                fontsize=7.5, color='#7F8C8D', transform=ax.transAxes)

    ax.legend(
        handles=[mpatches.Patch(facecolor='white', edgecolor=GOAL_COLOR,
                                linewidth=2.0, label='Goal satisfied')],
        loc='lower right', fontsize=7, framealpha=0.85)


# ── Direct plan generation ────────────────────────────────────────────────────

def _generate_hanoi_plan(initial: HanoiState, all_goals: list) -> list[str]:
    """Generate the Tower of Hanoi plan recursively — no planner call needed."""
    disc_on  = dict(initial.disc_on)
    disc_set = set(disc_on.keys())
    # Pegs that have discs on them + pegs that are clear (initially empty)
    peg_set  = (set(disc_on.values()) - disc_set) | (initial.clear - disc_set)

    # Build per-peg stacks (bottom → top)
    peg_stacks: dict[str, list[str]] = {p: [] for p in peg_set}
    for p in peg_set:
        cur = next((d for d, s in disc_on.items() if s == p), None)
        if cur is None:
            continue
        stack = [cur]
        while True:
            above = next((d for d, s in disc_on.items() if s == stack[-1]), None)
            if above is None:
                break
            stack.append(above)
        peg_stacks[p] = stack

    source_peg = next(p for p in peg_set if peg_stacks[p])
    disc_order = list(peg_stacks[source_peg])   # largest → smallest (bottom → top)

    goal_on  = {g[1].lower(): g[2].lower() for g in all_goals
                if g[0].lower() == 'on' and len(g) == 3}
    bottom   = disc_order[0]
    target_peg = goal_on[bottom]
    aux_peg    = next(p for p in sorted(peg_set) if p != source_peg and p != target_peg)

    plan: list[str] = []

    def move(disc: str, from_peg: str, to_peg: str) -> None:
        from_sup = disc_on[disc]
        to_sup   = peg_stacks[to_peg][-1] if peg_stacks[to_peg] else to_peg
        plan.append(CONNECTOR.join(['move', disc, from_sup, to_sup]))
        peg_stacks[from_peg].pop()
        peg_stacks[to_peg].append(disc)
        disc_on[disc] = to_sup

    def hanoi(k: int, src: str, tgt: str, aux: str) -> None:
        if k == 0:
            return
        disc = peg_stacks[src][-k] if k <= len(peg_stacks[src]) else peg_stacks[src][-1]
        # move top k-1 discs out of the way
        hanoi(k - 1, src, aux, tgt)
        move(peg_stacks[src][-1], src, tgt)
        hanoi(k - 1, aux, tgt, src)

    hanoi(len(disc_order), source_peg, target_peg, aux_peg)
    return plan


def _states_from_actions(initial: HanoiState, actions: list[str]) -> list[tuple]:
    states = [(initial.copy(), [])]
    cur    = initial.copy()
    for act in actions:
        cur = _apply_action(cur, act)
        states.append((cur.copy(), [act]))
    return states


# ── Full search + animation builder ───────────────────────────────────────────

def run_full_search(domain_file: str, problem_file: str, max_steps: int, debug: int):
    graph = PlanningGraph()
    graph.debug_flag = debug
    graph.load(domain_file, problem_file)
    graph.process_data()
    graph.create_graph(max_steps, auto_stop=False)
    initial     = _parse_initial_state(graph)
    discs, pegs = _parse_objects(graph)
    all_goals   = list(graph.the_goals)

    plan_actions = _generate_hanoi_plan(initial, all_goals)
    plan_states  = _states_from_actions(initial, plan_actions)
    plan_horizon = len(plan_actions)

    n_search  = min(3, plan_horizon - 1)
    step_size = max(1, plan_horizon // (n_search + 1))
    search_hs = list(range(step_size, plan_horizon, step_size))[:n_search]
    horizon_data: list = [(h, [(initial.copy(), [])], [], False) for h in search_hs]
    horizon_data.append((plan_horizon, plan_states, all_goals, True))

    return graph, plan_horizon, horizon_data, initial, discs, pegs, all_goals


def build_animation(domain_file: str, problem_file: str, max_steps: int, debug: int,
                    show_noop: bool, max_facts: int, max_actions: int, interval: int):
    print(f'Loading {domain_file} + {problem_file}')
    (graph, plan_horizon, horizon_data,
     initial, discs, pegs, all_goals) = run_full_search(
        domain_file, problem_file, max_steps, debug)

    disc_order  = _initial_tower_order(graph)
    peg_x       = _peg_xs(pegs)
    dwidths     = _disc_widths(disc_order)
    disc_colors = {d: DISC_PALETTE[i % len(DISC_PALETTE)]
                   for i, d in enumerate(disc_order)}
    goal_names  = {CONNECTOR.join(g) for g in all_goals}
    # list of (disc, support) from goal predicates
    goal_pairs  = [(g[1].lower(), g[2].lower()) for g in all_goals
                   if g[0].lower() == 'on' and len(g) == 3]
    num_layers  = len(graph.op_table)

    if plan_horizon < 0:
        print(f'No plan found within {max_steps} steps.')
    else:
        print(f'Plan found at horizon {plan_horizon}.')

    # Pre-compute positions for each state in each horizon
    horizon_positions = [
        [state_to_positions(s, discs, pegs, peg_x) for s, _ in plan_states]
        for _, plan_states, _, _ in horizon_data
    ]

    frame_ms        = max(20, interval // N_SUB)
    n_search_frames = max(1, SEARCH_MS // frame_ms)
    frames: list[dict] = []

    for hi, (h, plan_states, achieved, is_full) in enumerate(horizon_data):
        graph_layer = min(h - 1, num_layers - 1)
        n_goals     = len(all_goals)
        n_ach       = len(achieved)
        reachable_g = {
            CONNECTOR.join(g) for g in all_goals
            if h < len(graph.fact_table)
            and graph.fact_table[h].lookup(CONNECTOR.join(g)) is not None
        }
        pos_list = horizon_positions[hi]

        if not is_full:
            final_state, _ = plan_states[-1]
            sat = {d for d, sup in goal_pairs if final_state.disc_on.get(d) == sup}
            frame = dict(
                graph_layer=graph_layer, positions=pos_list[-1],
                goal_set=sat, step_num=len(plan_states) - 1,
                total_steps=len(plan_states) - 1, actions=[],
                title_extra=f'— {n_ach}/{n_goals} goals achievable',
                horizon=h, phase='search', reachable_goals=reachable_g,
            )
            for _ in range(n_search_frames):
                frames.append(frame)
        else:
            total_steps = len(plan_states) - 1
            for step_i in range(len(plan_states)):
                state, _   = plan_states[step_i]
                sat        = {d for d, sup in goal_pairs if state.disc_on.get(d) == sup}
                pos_start  = pos_list[step_i]
                if step_i + 1 < len(plan_states):
                    next_state, acts = plan_states[step_i + 1]
                    pos_end          = pos_list[step_i + 1]
                    subframes        = _step_subframes(pos_start, pos_end, discs)
                    for sfi, (sub_pos, _) in enumerate(subframes):
                        frames.append(dict(
                            graph_layer=graph_layer, positions=sub_pos, goal_set=sat,
                            step_num=step_i, total_steps=total_steps,
                            actions=acts if sfi >= N_SUB // 2 else [],
                            title_extra=f'— {n_goals}/{n_goals} goals',
                            horizon=h, phase='execute', reachable_goals=reachable_g,
                        ))
                else:
                    sat_final = {d for d, sup in goal_pairs if state.disc_on.get(d) == sup}
                    fr = dict(
                        graph_layer=graph_layer, positions=pos_start, goal_set=sat_final,
                        step_num=step_i, total_steps=total_steps, actions=[],
                        title_extra='— Goal achieved!',
                        horizon=h, phase='execute', reachable_goals=reachable_g,
                    )
                    for _ in range(N_SUB):
                        frames.append(fr)

    print(f'Animation: {len(frames)} frames at {frame_ms} ms each '
          f'({len(frames) * frame_ms / 1000:.1f}s total, loops)')

    fig = plt.figure(figsize=(16, 6))
    fig.patch.set_facecolor(C_BG)
    gs = GridSpec(1, 2, figure=fig, left=0.01, right=0.99, top=0.91, bottom=0.06,
                  wspace=0.04, width_ratios=[2, 1])
    ax_graph = fig.add_subplot(gs[0])
    ax_hanoi = fig.add_subplot(gs[1])

    def _suptitle(fr: dict) -> str:
        h = fr['horizon']
        if fr['phase'] == 'execute':
            return (f'Plan found at horizon {h}  —  '
                    f'Executing step {fr["step_num"]} / {fr["total_steps"]}')
        return f'Horizon {h}  —  Searching…  {fr["title_extra"]}'

    _last_layer = [-1]

    def update(fi: int):
        fr = frames[fi]
        t  = fr['graph_layer']
        rg = fr.get('reachable_goals', goal_names)
        if t != _last_layer[0] and t < len(graph.op_table):
            render_layer(ax_graph, graph, t, rg, show_noop=show_noop,
                         max_facts=max_facts, max_actions=max_actions)
            _last_layer[0] = t
        render_hanoi(ax_hanoi, fr['positions'], discs, pegs, peg_x, dwidths, disc_colors,
                     fr['goal_set'], fr['step_num'], fr['total_steps'],
                     fr['actions'], fr['title_extra'])
        fig.suptitle(_suptitle(fr), fontsize=12, fontweight='bold', color='#1B2631', y=0.97)
        fig.canvas.draw_idle()

    ani = manim.FuncAnimation(fig, update, frames=len(frames),
                               interval=frame_ms, repeat=True, blit=False)
    update(0)
    return fig, ani


# ── Entry point ───────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description='Animate Towers of Hanoi')
    parser.add_argument('-o', '--domain',      required=True)
    parser.add_argument('-f', '--problem',     required=True)
    parser.add_argument('--steps',       type=int, default=35)
    parser.add_argument('--interval',    type=int, default=1000)
    parser.add_argument('--save',        default=None)
    parser.add_argument('--no-noop',     action='store_true')
    parser.add_argument('--max-facts',   type=int, default=45)
    parser.add_argument('--max-actions', type=int, default=60)
    parser.add_argument('--debug',       type=int, default=0)
    args = parser.parse_args()

    _fig, ani = build_animation(
        domain_file=args.domain, problem_file=args.problem,
        max_steps=args.steps, debug=args.debug,
        show_noop=not args.no_noop,
        max_facts=args.max_facts, max_actions=args.max_actions,
        interval=args.interval,
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
