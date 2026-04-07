#!/usr/bin/env python3
"""
animate_blocksworld.py - Animate blocks-world plan search and execution.

Shows two panels side-by-side:
  Left  : Planning graph at the current horizon layer
  Right : Blocks-world state (smooth block movement)

Animation sequence
------------------
For each horizon h = 1, 2, …, T_final:
  • Show the planning graph at layer h-1
  • If graphplan cannot find a full plan: show the BEST PARTIAL PLAN that
    achieves the most goal states at this horizon, with its final state
  • If a full plan IS found at horizon h: animate the plan execution
    step-by-step with smooth sub-frame interpolation, then stop

Usage
-----
    python animate_blocksworld.py -o domain.pddl -f problem.pddl [options]

Options
-------
  --steps N        Max horizons to try (default: 12)
  --interval N     Milliseconds per logical plan step (default: 1200)
  --save PATH      Save animation as MP4 or GIF
  --no-noop        Hide NOOP actions in planning-graph panel
  --max-facts N    Max fact nodes per column (default: 45)
  --max-actions N  Max action nodes per column (default: 60)
  --debug N        Debug level (default: 0)
"""

from __future__ import annotations
import sys
import os
import argparse
import itertools

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import matplotlib.animation as manim
from matplotlib.gridspec import GridSpec

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from graphplan import PlanningGraph
from planner import Planner
from data_structures import CONNECTOR, NOOP, SolverSpec, Graphplan_Solver, Sat
from contextlib import contextmanager
from visualize_graphplan import C_BG


@contextmanager
def _goals_first(graph, t: int, goal_names: set):
    """Temporarily reorder fact_table[t] and fact_table[t+1] so goal facts come first.

    render_layer truncates to max_facts items.  By moving goal facts to the
    front of the internal dict the goals are always within the visible window
    in both the left (facts@t) and right (facts@t+1) columns.
    """
    saved = []
    for layer in (t, t + 1):
        if layer < len(graph.fact_table):
            ft   = graph.fact_table[layer]
            orig = dict(ft._dict)
            goals  = {k: v for k, v in orig.items() if k in goal_names}
            others = {k: v for k, v in orig.items() if k not in goal_names}
            ft._dict = {**goals, **others}
            saved.append((ft, orig))
    try:
        yield
    finally:
        for ft, orig in saved:
            ft._dict = orig


# ── Layout constants ──────────────────────────────────────────────────────────
N_SUB        = 12    # sub-frames per EXECUTION step (20 fps × ~0.6s per step)
SEARCH_MS    = 500  # how long each search-phase frame is shown (milliseconds)
FRAME_MS     = 50   # ms per rendered frame → 20 fps
ARM_Y    = 0.72   # y-centre of held block (arm height)
ARM_EXT  = 0.13   # arm line length above held block
TABLE_Y  = 0.10   # y of table surface
BLOCK_H  = 0.05   # block height (fixed; stacks grow upward)
GAP      = 0.004

# BLOCK_W is computed dynamically per render call so it scales with n_blocks.
# Use _block_w(n_cols) everywhere instead of a hard constant.
def _block_w(n_cols: int) -> float:
    slot_w = 0.96 / max(n_cols, 1)
    return min(0.13, slot_w * 0.82)


def _label_fs(n_cols: int) -> float:
    """Font size for block labels, smaller when many blocks."""
    return max(6.0, min(10.0, 10.0 - max(0, n_cols - 5) * 0.6))

_BLOCK_PALETTE = [
    '#E74C3C', '#3498DB', '#2ECC71', '#F39C12',
    '#9B59B6', '#1ABC9C', '#E67E22', '#34495E',
]
BG_BLOCKS    = '#FAFAFA'
GOAL_OUTLINE = '#27AE60'
ARM_COLOR    = '#607D8B'


# ── Blocks-world state ────────────────────────────────────────────────────────

class BWState:
    def __init__(self):
        self.on:        dict[str, str] = {}
        self.ontable:   set[str]       = set()
        self.clear:     set[str]       = set()
        self.handempty: bool           = True
        self.holding:   str | None     = None

    def copy(self) -> 'BWState':
        s = BWState()
        s.on        = dict(self.on)
        s.ontable   = set(self.ontable)
        s.clear     = set(self.clear)
        s.handempty = self.handempty
        s.holding   = self.holding
        return s


def _parse_initial_state(graph: PlanningGraph) -> BWState:
    s = BWState()
    for fact in graph.initial_facts:
        pred = fact[0].lower()
        args = [a.lower() for a in fact[1:]]
        if pred == 'on' and len(args) == 2:
            s.on[args[0]] = args[1]
        elif pred == 'ontable' and len(args) == 1:
            s.ontable.add(args[0])
        elif pred == 'clear' and len(args) == 1:
            s.clear.add(args[0])
        elif pred == 'handempty':
            s.handempty = True
        elif pred == 'holding' and len(args) == 1:
            s.handempty = False
            s.holding   = args[0]
    return s


def _parse_action(action_name: str) -> tuple[str, list[str]]:
    name = action_name.lower()
    for prefix in ('pick-up', 'put-down', 'unstack', 'stack'):
        if name.startswith(prefix + CONNECTOR):
            rest = name[len(prefix) + len(CONNECTOR):]
            return prefix, rest.split(CONNECTOR)
    parts = name.split(CONNECTOR)
    return parts[0], parts[1:]


def _apply_action(s: BWState, action_name: str) -> BWState:
    if NOOP in action_name.lower():
        return s.copy()
    ns = s.copy()
    atype, args = _parse_action(action_name)
    if atype == 'pick-up' and args:
        x = args[0]
        ns.ontable.discard(x); ns.clear.discard(x)
        ns.handempty = False; ns.holding = x
    elif atype == 'put-down' and args:
        x = args[0]
        ns.holding = None; ns.handempty = True
        ns.ontable.add(x); ns.clear.add(x)
    elif atype == 'stack' and len(args) >= 2:
        x, y = args[0], args[1]
        ns.holding = None; ns.handempty = True
        ns.clear.discard(y); ns.clear.add(x); ns.on[x] = y
    elif atype == 'unstack' and len(args) >= 2:
        x, y = args[0], args[1]
        ns.on.pop(x, None); ns.clear.add(y)
        ns.clear.discard(x); ns.handempty = False; ns.holding = x
    return ns


def _build_stacks(state: BWState, all_blocks: list[str]) -> list[list[str]]:
    bottoms = set(state.ontable)
    for b in all_blocks:
        if b not in state.on and b not in bottoms and state.holding != b:
            bottoms.add(b)
    stacks = []
    for bot in sorted(bottoms):
        stack = [bot]
        cur = bot
        while True:
            above = sorted(b for b, below in state.on.items() if below == cur)
            if not above:
                break
            cur = above[0]
            stack.append(cur)
        stacks.append(stack)
    return stacks


def _extract_plan_states(graph: PlanningGraph, maxtime: int,
                         initial: BWState) -> list[tuple[BWState, list[str]]]:
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


# ── Position system ───────────────────────────────────────────────────────────

def _ease(t: float) -> float:
    """Smooth-step: zero velocity at both endpoints."""
    return t * t * (3.0 - 2.0 * t)


def _step_subframes(
        pos_start: dict, pos_end: dict,
        hold_start: str | None, hold_end: str | None,
        acts: list[str], all_blocks: list[str],
) -> list[tuple[dict, str | None]]:
    """Return N_SUB (positions, holding) pairs for one plan step.

    Uses a three-phase robotic-arm trajectory instead of diagonal lerp:
      • Lift    – block rises straight up to ARM_Y   (pick-up / unstack)
      • Slide   – arm moves horizontally at ARM_Y    (stack / put-down with Δx)
      • Lower   – block descends straight down        (stack / put-down)

    This makes the motion look physically natural: the arm always lifts
    clear of obstacles before moving sideways, then lowers onto the target.
    """
    moving = [b for b in all_blocks if pos_start.get(b) != pos_end.get(b)]

    # No movement this step — hold position
    if not moving or not acts:
        return [(dict(pos_start), hold_start)] * N_SUB

    mb = moving[0]
    sx, sy = pos_start.get(mb, pos_end[mb])
    ex, ey = pos_end.get(mb, pos_start[mb])
    atype, _ = _parse_action(acts[0])

    # ── Build phase list: each phase = ((x0,y0), (x1,y1), holding_during) ──
    if atype in ('pick-up', 'unstack'):
        # Block is on a surface → lift straight up to ARM_Y
        phases = [((sx, sy), (sx, ARM_Y), hold_end)]

    elif atype in ('put-down', 'stack'):
        # Block is held at (sx, ARM_Y); needs to reach (ex, ey)
        if abs(sx - ex) < 0.004:
            # Already directly above destination: just lower
            phases = [((sx, ARM_Y), (ex, ey), hold_start)]
        else:
            # Slide horizontally first, then lower
            phases = [
                ((sx, ARM_Y), (ex, ARM_Y), hold_start),   # slide
                ((ex, ARM_Y), (ex, ey),    hold_start),   # lower
            ]
    else:
        phases = [((sx, sy), (ex, ey), hold_start)]

    # ── Distribute N_SUB frames evenly among phases ───────────────────────
    n_phases   = len(phases)
    base_n     = N_SUB // n_phases
    remainder  = N_SUB - base_n * n_phases   # extra frames go to last phase

    result: list[tuple[dict, str | None]] = []
    for pi, ((x0, y0), (x1, y1), holding_during) in enumerate(phases):
        n_frames   = base_n + (remainder if pi == n_phases - 1 else 0)
        is_last    = pi == n_phases - 1

        for fi in range(n_frames):
            # t goes 1/n → 1 (skip t=0 so we don't repeat the previous endpoint)
            t  = (fi + 1) / n_frames
            et = _ease(t)
            pos          = dict(pos_start)
            pos[mb]      = (x0 + (x1 - x0) * et, y0 + (y1 - y0) * et)
            # Release the block at the very last frame of the last phase
            holding_here = hold_end if (is_last and fi == n_frames - 1) else holding_during
            result.append((pos, holding_here))

    return result


def state_to_positions(state: BWState, all_blocks: list[str],
                       initial_slots: dict[str, int],
                       prev_positions: dict | None = None
                       ) -> dict[str, tuple[float, float]]:
    """Compute block centre (cx, cy) using fixed column layout.

    Each block always occupies the column of the BOTTOM block in its stack
    (using alphabetical initial ordering).  This prevents non-acting blocks
    from shifting sideways when stacks merge or split.

    When *prev_positions* is given, newly-held blocks keep their cx from
    the previous frame (arm stays above where the block was).
    """
    n_cols  = len(all_blocks)
    slot_w  = 0.96 / n_cols
    stacks  = _build_stacks(state, all_blocks)
    pos: dict[str, tuple[float, float]] = {}

    for stack in stacks:
        col = initial_slots.get(stack[0], 0)
        cx  = 0.02 + slot_w * col + slot_w / 2
        for bi, block in enumerate(stack):
            cy = TABLE_Y + BLOCK_H / 2 + GAP + bi * (BLOCK_H + GAP)
            pos[block] = (cx, cy)

    if state.holding:
        if prev_positions and state.holding in prev_positions:
            cx = prev_positions[state.holding][0]   # keep arm above origin
        else:
            col = initial_slots.get(state.holding, 0)
            cx  = 0.02 + slot_w * col + slot_w / 2
        pos[state.holding] = (cx, ARM_Y)

    return pos


# ── Blocks-world renderer ─────────────────────────────────────────────────────

def render_blocksworld_positioned(
        ax,
        positions:    dict[str, tuple[float, float]],
        holding:      str | None,
        all_blocks:   list[str],
        goal_blocks:  set[str],
        block_colors: dict[str, str],
        step_num:     int,
        total_steps:  int,
        actions:      list[str],
        title_extra:  str = ''):
    """Draw the blocks world using explicit per-block positions.

    *goal_blocks* is the set of block names that appear as ARGUMENTS to
    any goal predicate (used for green-border highlighting).
    """
    ax.clear()
    ax.set_facecolor(BG_BLOCKS)
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.axis('off')

    n_cols = len(all_blocks)
    bw     = _block_w(n_cols)
    fs     = _label_fs(n_cols)

    # Table surface
    ax.add_patch(mpatches.FancyBboxPatch(
        (0.02, TABLE_Y - 0.015), 0.96, 0.015,
        boxstyle='round,pad=0.001',
        facecolor='#A1887F', edgecolor='#795548', linewidth=1.5, zorder=2))

    # Arm + gripper (drawn behind blocks)
    if holding and holding in positions:
        cx, cy = positions[holding]
        arm_top = min(cy + BLOCK_H / 2 + ARM_EXT, 0.96)
        ax.plot([cx, cx], [cy + BLOCK_H / 2, arm_top],
                color=ARM_COLOR, linewidth=4, solid_capstyle='round', zorder=3)
        hw = bw * 0.22
        gy = cy + BLOCK_H / 2 + 0.008
        ax.plot([cx - hw, cx + hw], [gy, gy],
                color=ARM_COLOR, linewidth=3, solid_capstyle='round', zorder=3)

    # Blocks
    for block in all_blocks:
        if block not in positions:
            continue
        cx, cy = positions[block]
        fc  = block_colors.get(block, '#CCCCCC')
        # Highlight only if this exact block is a goal argument
        is_goal = block.lower() in goal_blocks
        ec = GOAL_OUTLINE if is_goal else '#555555'
        lw = 2.0 if is_goal else 0.9
        ax.add_patch(mpatches.FancyBboxPatch(
            (cx - bw / 2, cy - BLOCK_H / 2), bw, BLOCK_H,
            boxstyle='round,pad=0.003',
            facecolor=fc, edgecolor=ec, linewidth=lw, zorder=4))
        ax.text(cx, cy, block.upper(),
                ha='center', va='center',
                fontsize=fs, fontweight='bold', color='white', zorder=5)

    # Status text
    ax.text(0.5, 0.97,
            f'Step {step_num} / {total_steps}  {title_extra}',
            ha='center', va='top', fontsize=9, fontweight='bold',
            color='#1B2631', transform=ax.transAxes)

    if actions:
        ax.text(0.5, 0.93,
                'Actions: ' + ',  '.join(_pretty_action(a) for a in actions),
                ha='center', va='top', fontsize=7.5, color='#2C3E50',
                transform=ax.transAxes)
    else:
        ax.text(0.5, 0.93, '(initial state)',
                ha='center', va='top', fontsize=7.5, color='#7F8C8D',
                transform=ax.transAxes)

    goal_patch = mpatches.Patch(facecolor='white', edgecolor=GOAL_OUTLINE,
                                linewidth=2.0, label='Goal block/pos')
    ax.legend(handles=[goal_patch], loc='lower right', fontsize=7, framealpha=0.85)


# ── Best partial plan ─────────────────────────────────────────────────────────

def find_best_partial_plan(
        graph:         PlanningGraph,
        planner:       Planner,
        all_goals:     list,
        h:             int,
        initial:       BWState,
        initial_slots: dict[str, int],
        all_blocks:    list[str],
        max_calls:     int = 150,
) -> tuple[list[tuple[BWState, list[str]]], list]:
    """Return (plan_states, achieved_goals) for the largest satisfiable
    subset of *all_goals* at horizon *h*.

    Strategy
    --------
    1. **Graph-reachability filter**: skip any goal not yet in the planning
       graph at layer *h* — these are definitely unsatisfiable.
    2. **can_stop pre-filter**: before calling the backward-chaining planner,
       call ``graph.can_stop(h)`` for the candidate subset.  This checks both
       reachability and pairwise non-mutex in O(k²) time — far cheaper than
       a full planner call.  Subsets that fail can_stop are skipped without
       counting against the call budget.
    3. **Call cap**: limit expensive planner calls to *max_calls*.
    4. **Guaranteed size-1 fallback**: after the main search (even if the cap
       is hit), always sweep individual goals.  This ensures that at least one
       goal is shown at every horizon where any single goal is achievable —
       regardless of how many larger subsets were explored.
    """
    original_goals = list(graph.the_goals)
    best_states: list[tuple[BWState, list[str]]] = [(initial, [])]
    best_goals:  list = []
    calls = 0

    # 1. Goals whose fact is present in the planning graph at this horizon
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

    # 2. Main search: sizes n down to 2 (size-1 handled by the fallback below)
    n = len(reachable_idx)
    for size in range(n, 1, -1):
        found = False
        for indices in itertools.combinations(reachable_idx, size):
            # Cheap pre-filter: skip mutex-conflicted subsets
            graph.the_goals = [all_goals[i] for i in indices]
            if not graph.can_stop(h):
                continue                     # free — doesn't cost a call

            if calls >= max_calls:
                break                        # inner loop only
            calls += 1
            if planner.do_plan(h) == Sat:
                best_states = _extract_plan_states(graph, h, initial)
                best_goals  = list(graph.the_goals)
                found = True
                break
        if found:
            break
        if calls >= max_calls:
            break

    # 3. Guaranteed size-1 fallback: always try individual goals.
    #    This runs even when the cap is hit so we never show zero goals
    #    at a horizon where at least one goal is individually achievable.
    if not best_goals:
        for idx in reachable_idx:
            graph.the_goals = [all_goals[idx]]
            if planner.do_plan(h) == Sat:
                best_states = _extract_plan_states(graph, h, initial)
                best_goals  = [all_goals[idx]]
                break

    graph.the_goals = original_goals
    return best_states, best_goals


# ── Search ────────────────────────────────────────────────────────────────────

def run_full_search(domain_file: str, problem_file: str,
                    max_steps: int, debug: int):
    """Build graph and collect per-horizon best plans.

    Returns (graph, plan_horizon, horizon_data, initial, all_blocks,
             initial_slots, all_goals).
    horizon_data: list of (h, plan_states, achieved_goals, is_full).
    """
    graph = PlanningGraph()
    graph.debug_flag = debug
    graph.load(domain_file, problem_file)
    graph.process_data()

    initial = _parse_initial_state(graph)
    all_blocks = sorted({b.lower() for fact in graph.initial_facts
                         for b in fact[1:]
                         if fact[0].lower() in ('on', 'ontable', 'clear', 'holding')})
    initial_slots = {b: i for i, b in enumerate(all_blocks)}

    # Build entire graph first so all layers exist for visualisation
    graph.create_graph(max_steps, auto_stop=False)

    all_goals = list(graph.the_goals)
    planner   = Planner(
        graph=graph,
        solver_specs=[SolverSpec(solver_name='graphplan',
                                 solver_type=Graphplan_Solver)],
        debug=debug, noopt=True, do_justify=False,
    )

    horizon_data = []
    plan_horizon = -1

    for h in range(1, max_steps + 1):
        if h >= len(graph.fact_table):
            break
        states, achieved = find_best_partial_plan(
            graph, planner, all_goals, h, initial, initial_slots, all_blocks
        )
        is_full = (len(achieved) == len(all_goals))
        horizon_data.append((h, states, achieved, is_full))
        if is_full:
            plan_horizon = h
            break

    return graph, plan_horizon, horizon_data, initial, all_blocks, initial_slots, all_goals


# ── Animation ─────────────────────────────────────────────────────────────────

def build_animation(domain_file: str, problem_file: str,
                    max_steps: int, debug: int,
                    show_noop: bool, max_facts: int, max_actions: int,
                    interval: int, use_clustered: bool = False):
    """Build and return (fig, FuncAnimation).

    *interval* = milliseconds per logical plan step.
    Sub-frames run at interval // N_SUB ms each.
    Search frames each last *interval* ms (repeated N_SUB times).
    """
    if use_clustered:
        from visualize_graphplan_clustered import render_layer
    else:
        from visualize_graphplan import render_layer

    print(f'Loading {domain_file} + {problem_file}')
    (graph, plan_horizon, horizon_data,
     initial, all_blocks, initial_slots, all_goals) = run_full_search(
        domain_file, problem_file, max_steps, debug)

    goal_names_raw = {CONNECTOR.join(g) for g in graph.the_goals}
    # Block names that appear as *arguments* to goal predicates (for highlighting)
    goal_blocks    = {a.lower() for g in graph.the_goals for a in g[1:]}
    num_layers     = len(graph.op_table)

    if plan_horizon < 0:
        print(f'No plan found within {max_steps} steps.')
    else:
        total_acts = sum(len(a) for _, a in horizon_data[-1][1])
        print(f'Plan found at horizon {plan_horizon}  ({total_acts} real actions)')

    block_colors = {b: _BLOCK_PALETTE[i % len(_BLOCK_PALETTE)]
                    for i, b in enumerate(all_blocks)}

    # ── Pre-compute per-state positions ───────────────────────────────────
    # horizon_positions[hi] = list of pos dicts, one per plan state
    horizon_positions: list[list[dict]] = []
    for h, plan_states, achieved, is_full in horizon_data:
        pos_list: list[dict] = []
        prev = None
        for bw_state, _ in plan_states:
            p = state_to_positions(bw_state, all_blocks, initial_slots, prev)
            pos_list.append(p)
            prev = p
        horizon_positions.append(pos_list)

    # ── Build frame list ──────────────────────────────────────────────────
    # Frame = dict with keys used by update()
    frames: list[dict] = []
    # Fixed 20 fps (FRAME_MS ms per frame).
    # Search frames each last SEARCH_MS ms; execution uses N_SUB sub-frames.
    sub_interval    = FRAME_MS
    n_search_frames = max(1, SEARCH_MS // FRAME_MS)   # frames per search horizon

    for hi, (h, plan_states, achieved, is_full) in enumerate(horizon_data):
        graph_layer  = min(h - 1, num_layers - 1)
        pos_list     = horizon_positions[hi]
        n_goals      = len(all_goals)
        n_achieved   = len(achieved)

        # Goals reachable at this horizon (for graph highlighting)
        reachable_g = {
            CONNECTOR.join(g) for g in all_goals
            if h < len(graph.fact_table)
               and graph.fact_table[h].lookup(CONNECTOR.join(g)) is not None
        }

        if not is_full:
            # ── Search frame ─────────────────────────────────────────────
            final_state, _ = plan_states[-1]
            final_pos       = pos_list[-1]
            n_steps         = len(plan_states) - 1
            title_extra     = (f'— {n_achieved}/{n_goals} goals achievable simultaneously'
                               if n_achieved else '— no goals achievable simultaneously yet')
            frame = dict(
                graph_layer     = graph_layer,
                positions       = final_pos,
                holding         = final_state.holding,
                step_num        = n_steps,
                total_steps     = n_steps,
                actions         = [],
                title_extra     = title_extra,
                horizon         = h,
                phase           = 'search',
                reachable_goals = reachable_g,
            )
            for _ in range(n_search_frames):   # hold for SEARCH_MS total
                frames.append(frame)

        else:
            # ── Execution frames (smooth sub-frame interpolation) ─────────
            total_steps = len(plan_states) - 1

            for step_i in range(len(plan_states)):
                bw_state, _ = plan_states[step_i]
                pos_start    = pos_list[step_i]
                hold_start   = bw_state.holding

                if step_i + 1 < len(plan_states):
                    # acts that PRODUCE next_state from current state
                    next_state, acts = plan_states[step_i + 1]
                    pos_end          = pos_list[step_i + 1]
                    hold_end         = next_state.holding

                    # Multi-phase trajectory: lift → slide → lower
                    subframes = _step_subframes(
                        pos_start, pos_end,
                        hold_start, hold_end,
                        acts, all_blocks,
                    )

                    for sub_i, (sub_pos, sub_hold) in enumerate(subframes):
                        # Show action label in the second half of the step
                        sub_acts = acts if sub_i >= N_SUB // 2 else []
                        frames.append(dict(
                            graph_layer     = graph_layer,
                            positions       = sub_pos,
                            holding         = sub_hold,
                            step_num        = step_i,
                            total_steps     = total_steps,
                            actions         = sub_acts,
                            title_extra     = f'— {n_goals}/{n_goals} goals',
                            horizon         = h,
                            phase           = 'execute',
                            reachable_goals = reachable_g,
                        ))
                else:
                    # Final state: hold for N_SUB ticks
                    frame = dict(
                        graph_layer     = graph_layer,
                        positions       = pos_start,
                        holding         = hold_start,
                        step_num        = step_i,
                        total_steps     = total_steps,
                        actions         = [],
                        title_extra     = '— Goal achieved!',
                        horizon         = h,
                        phase           = 'execute',
                        reachable_goals = reachable_g,
                    )
                    for _ in range(N_SUB):
                        frames.append(frame)

    print(f'Animation: {len(frames)} frames at {sub_interval} ms each '
          f'({len(frames) * sub_interval / 1000:.1f}s total, loops)')

    # ── Figure setup ──────────────────────────────────────────────────────
    fig = plt.figure(figsize=(22, 10))
    fig.patch.set_facecolor(C_BG)
    gs = GridSpec(1, 2, figure=fig,
                  left=0.01, right=0.99, top=0.91, bottom=0.06,
                  wspace=0.04, width_ratios=[2, 1])
    ax_graph  = fig.add_subplot(gs[0])
    ax_blocks = fig.add_subplot(gs[1])

    def _suptitle(fr: dict) -> str:
        h     = fr['horizon']
        phase = fr['phase']
        if phase == 'execute':
            s, t = fr['step_num'], fr['total_steps']
            return f'Plan found at horizon {h}  —  Executing step {s} / {t}'
        return f'Horizon {h}  —  Searching…  {fr["title_extra"]}'

    def update(frame_idx: int):
        fr = frames[frame_idx]
        t  = fr['graph_layer']
        reachable_g = fr.get('reachable_goals', goal_names_raw)
        if t < len(graph.op_table):
            with _goals_first(graph, t, reachable_g):
                render_layer(ax_graph, graph, t, reachable_g,
                             show_noop=show_noop,
                             max_facts=max_facts, max_actions=max_actions)
        render_blocksworld_positioned(
            ax_blocks,
            fr['positions'], fr['holding'],
            all_blocks, goal_blocks, block_colors,
            fr['step_num'], fr['total_steps'],
            fr['actions'],  fr['title_extra'],
        )
        fig.suptitle(_suptitle(fr), fontsize=12, fontweight='bold',
                     color='#1B2631', y=0.97)
        fig.canvas.draw_idle()

    ani = manim.FuncAnimation(
        fig, update,
        frames=len(frames),
        interval=sub_interval,
        repeat=True, blit=False,
    )
    update(0)
    return fig, ani


# ── Entry point ───────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description='Animate blocks-world plan search and execution',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument('-o', '--domain',     required=True)
    parser.add_argument('-f', '--problem',    required=True)
    parser.add_argument('--steps',     type=int, default=34,
                        help='Max horizons to try (default: 20)')
    parser.add_argument('--interval',  type=int, default=1200,
                        help='Ms per logical plan step (default: 1200)')
    parser.add_argument('--save',      default=None,
                        help='Save as MP4 or GIF')
    parser.add_argument('--no-noop',   action='store_true')
    parser.add_argument('--max-facts',   type=int, default=45)
    parser.add_argument('--max-actions', type=int, default=60)
    parser.add_argument('--debug',       type=int, default=0)
    parser.add_argument('--clustered',   action='store_true',
                        help='Use predicate-clustered graph renderer')
    args = parser.parse_args()

    _fig, ani = build_animation(
        domain_file   = args.domain,
        problem_file  = args.problem,
        max_steps     = args.steps,
        debug         = args.debug,
        show_noop     = not args.no_noop,
        max_facts     = args.max_facts,
        max_actions   = args.max_actions,
        interval      = args.interval,
        use_clustered = args.clustered,
    )

    if args.save:
        print(f'Saving to {args.save} …')
        ext = os.path.splitext(args.save)[1].lower()
        fps = max(1, 1000 // max(40, args.interval // N_SUB))
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
