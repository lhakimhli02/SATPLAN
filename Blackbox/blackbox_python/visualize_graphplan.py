#!/usr/bin/env python3
"""
visualize_graphplan.py - Visualize the BlackBox planning graph layer by layer.

Each layer t shows three columns:
  Facts @ t  |  Actions @ t  |  Facts @ t+1

Node colors:
  Blue   = fact
  Yellow = goal fact
  Green  = real action
  Gray   = NOOP action
  Red border = node has at least one mutex partner

Edges:
  Dark  = precondition (fact → action)
  Green = positive effect (action → fact)
  Red   = delete effect (action → fact)
  Red arc = mutex pair (up to 25 per column shown)

Usage:
    python visualize_graphplan.py -o domain.pddl -f problem.pddl [options]

Navigation (interactive mode):
    Left / Right arrow keys   previous / next layer
    s                         save current layer as PNG
    q  or  Escape             quit

Options:
    --steps N         Layers to build (default: 8)
    --max-facts N     Max fact nodes per column (default: 45)
    --max-actions N   Max action nodes per column (default: 60)
    --no-noop         Hide NOOP actions
    --save-all        Save every layer as a PNG and exit
    --out-dir DIR     Directory for saved PNGs  (default: graphplan_viz/)
"""

import sys
import os
import argparse

import matplotlib
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.collections import LineCollection
from matplotlib.lines import Line2D

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from graphplan import PlanningGraph
from data_structures import CONNECTOR, NOOP

# ── Colour scheme ─────────────────────────────────────────────────────────────
C_FACT   = '#AED6F1'   # light blue
C_GOAL   = '#F9E79F'   # yellow
C_ACTION = '#A9DFBF'   # light green
C_NOOP   = '#D5D8DC'   # light grey
C_MUTEX  = '#E74C3C'   # red
C_PRE    = '#2C3E50'   # dark – precondition edges
C_EFF    = '#1E8449'   # green – positive effect edges
C_DEL    = '#C0392B'   # dark red – delete effect edges
C_BG     = '#FAFAFA'


# ── Helpers ───────────────────────────────────────────────────────────────────

def _short(name: str, max_len: int = 24) -> str:
    """Underscore-joined name → space-separated, truncated."""
    s = name.replace(CONNECTOR, ' ')
    return s if len(s) <= max_len else s[:max_len - 2] + '..'


def _col_positions(n: int, x: float,
                   y_lo: float = 0.02, y_hi: float = 0.95) -> list:
    """(x, y) positions for n nodes evenly spaced vertically at column x."""
    if n == 0:
        return []
    if n == 1:
        return [(x, (y_lo + y_hi) / 2)]
    step = (y_hi - y_lo) / (n - 1)
    return [(x, y_hi - i * step) for i in range(n)]


def _draw_edges(ax, src_map: dict, dst_map: dict, pairs: list,
                color: str, alpha: float, lw: float,
                x_off_src: float = 0.0, x_off_dst: float = 0.0):
    """Draw a batch of edges as a LineCollection (fast)."""
    segs = []
    for s, d in pairs:
        if s in src_map and d in dst_map:
            x1, y1 = src_map[s]
            x2, y2 = dst_map[d]
            segs.append([(x1 + x_off_src, y1), (x2 + x_off_dst, y2)])
    if segs:
        ax.add_collection(
            LineCollection(segs, colors=color, linewidths=lw,
                           alpha=alpha, zorder=1))


def _draw_nodes(ax, vertices: list, positions: list,
                goal_names: set, node_w: float, node_h: float,
                is_action: bool):
    """Draw a column of rectangular nodes."""
    for v, (x, y) in zip(vertices, positions):
        if is_action:
            face = C_NOOP if v.is_noop else C_ACTION
        else:
            face = C_GOAL if v.name in goal_names else C_FACT

        has_mutex = bool(v.exclusive)
        edge_c = C_MUTEX if has_mutex else '#566573'
        lw     = 1.2    if has_mutex else 0.5

        ax.add_patch(mpatches.FancyBboxPatch(
            (x - node_w / 2, y - node_h / 2), node_w, node_h,
            boxstyle='round,pad=0.002',
            facecolor=face, edgecolor=edge_c, linewidth=lw, zorder=3))

        # Character budget based on node width in data-units
        chars = max(10, int(node_w * 155))
        ax.text(x, y, _short(v.name, chars),
                ha='center', va='center', fontsize=5,
                fontfamily='monospace', color='#1A1A1A', zorder=4)


def _draw_mutex_arcs(ax, vertices: list, positions: list, max_arcs: int = 25):
    """Curved red arcs for mutex pairs (limited to avoid clutter)."""
    pos_map = {v.name: p for v, p in zip(vertices, positions)}
    seen, drawn = set(), 0
    for v in vertices:
        if v.name not in pos_map:
            continue
        for excl in v.exclusive:
            if excl.name not in pos_map:
                continue
            key = tuple(sorted([v.name, excl.name]))
            if key in seen:
                continue
            seen.add(key)
            if drawn >= max_arcs:
                continue
            drawn += 1
            x1, y1 = pos_map[v.name]
            x2, y2 = pos_map[excl.name]
            ax.annotate('', xy=(x2, y2), xytext=(x1, y1),
                        arrowprops=dict(arrowstyle='-',
                                        connectionstyle='arc3,rad=0.5',
                                        color=C_MUTEX, lw=0.7, alpha=0.45),
                        zorder=2)
    return len(seen)


# ── Main render ───────────────────────────────────────────────────────────────

def render_layer(ax, graph: PlanningGraph, t: int,
                 goal_names: set, show_noop: bool,
                 max_facts: int, max_actions: int):
    """Render planning-graph layer t onto axes ax."""
    ax.clear()
    ax.set_xlim(-0.02, 1.02)
    ax.set_ylim(-0.08, 1.10)
    ax.axis('off')
    ax.set_facecolor(C_BG)

    # ── Collect nodes ─────────────────────────────────────────────────────
    all_ft   = list(graph.fact_table[t])
    all_ft1  = list(graph.fact_table[t + 1]) if t + 1 < len(graph.fact_table) else []
    all_ops  = list(graph.op_table[t])        if t     < len(graph.op_table)   else []

    real_ops  = [op for op in all_ops if not op.is_noop]
    noop_ops  = [op for op in all_ops if     op.is_noop]
    disp_ops  = real_ops + (noop_ops if show_noop else [])

    trunc_ft  = len(all_ft)   > max_facts
    trunc_ops = len(disp_ops) > max_actions
    trunc_ft1 = len(all_ft1)  > max_facts

    facts_t  = all_ft[:max_facts]
    ops      = disp_ops[:max_actions]
    facts_t1 = all_ft1[:max_facts]

    # ── Layout ────────────────────────────────────────────────────────────
    X_L, X_M, X_R = 0.08, 0.50, 0.92
    node_w = 0.165
    n_max  = max(len(facts_t), len(ops), len(facts_t1), 1)
    node_h = min(0.030, 0.88 / n_max * 0.80)

    pos_ft  = _col_positions(len(facts_t),  X_L)
    pos_ops = _col_positions(len(ops),      X_M)
    pos_ft1 = _col_positions(len(facts_t1), X_R)

    ft_map  = {v.name: p for v, p in zip(facts_t,  pos_ft)}
    op_map  = {v.name: p for v, p in zip(ops,       pos_ops)}
    ft1_map = {v.name: p for v, p in zip(facts_t1,  pos_ft1)}

    hw = node_w / 2  # half-width offset so edges meet node edges

    # ── Edges ─────────────────────────────────────────────────────────────
    _draw_edges(ax, ft_map, op_map,
                [(p.name, op.name) for op in ops for p in op.in_edges],
                C_PRE, alpha=0.22, lw=0.35, x_off_src=hw, x_off_dst=-hw)

    _draw_edges(ax, op_map, ft1_map,
                [(op.name, e.name) for op in ops for e in op.out_edges],
                C_EFF, alpha=0.28, lw=0.35, x_off_src=hw, x_off_dst=-hw)

    _draw_edges(ax, op_map, ft1_map,
                [(op.name, d.name) for op in ops for d in op.del_edges],
                C_DEL, alpha=0.22, lw=0.35, x_off_src=hw, x_off_dst=-hw)

    # ── Mutex arcs ────────────────────────────────────────────────────────
    fm_total = sum(len(v.exclusive)  for v in all_ft)  // 2
    om_total = sum(len(op.exclusive) for op in all_ops) // 2

    _draw_mutex_arcs(ax, facts_t,  pos_ft,  max_arcs=25)
    _draw_mutex_arcs(ax, ops,      pos_ops, max_arcs=25)

    # ── Nodes ─────────────────────────────────────────────────────────────
    _draw_nodes(ax, facts_t,  pos_ft,  goal_names, node_w, node_h, is_action=False)
    _draw_nodes(ax, ops,      pos_ops, goal_names, node_w, node_h, is_action=True)
    _draw_nodes(ax, facts_t1, pos_ft1, goal_names, node_w, node_h, is_action=False)

    # ── Column headers ────────────────────────────────────────────────────
    def shown_str(displayed, total, trunc):
        return f'{displayed}/{total}' if trunc else str(displayed)

    ax.text(X_L, 1.01,
            f'Facts @ t={t}\n[{shown_str(len(facts_t), len(all_ft), trunc_ft)} shown]',
            ha='center', va='bottom', fontsize=8, fontweight='bold', color='#1B2631')
    ax.text(X_M, 1.01,
            f'Actions @ t={t}\n[{shown_str(len(ops), len(disp_ops), trunc_ops)} shown'
            f' | {len(real_ops)} real, {len(noop_ops)} noop]',
            ha='center', va='bottom', fontsize=8, fontweight='bold', color='#1B2631')
    ax.text(X_R, 1.01,
            f'Facts @ t={t+1}\n[{shown_str(len(facts_t1), len(all_ft1), trunc_ft1)} shown]',
            ha='center', va='bottom', fontsize=8, fontweight='bold', color='#1B2631')

    # ── Mutex stats ───────────────────────────────────────────────────────
    ax.text(0.5, -0.055,
            f'Fact mutexes: {fm_total}  |  Action mutexes: {om_total}  '
            f'|  Red border = has mutex  |  Red arc = mutex pair (≤25 shown per column)',
            ha='center', va='top', fontsize=6.5, color='#922B21',
            transform=ax.transAxes)

    # ── Legend ────────────────────────────────────────────────────────────
    legend = [
        mpatches.Patch(facecolor=C_FACT,   edgecolor='#566573', label='Fact'),
        mpatches.Patch(facecolor=C_GOAL,   edgecolor='#566573', label='Goal fact'),
        mpatches.Patch(facecolor=C_ACTION, edgecolor='#566573', label='Action'),
        mpatches.Patch(facecolor=C_NOOP,   edgecolor='#566573', label='NOOP'),
        Line2D([0], [0], color=C_PRE,   lw=1.3, label='Precondition'),
        Line2D([0], [0], color=C_EFF,   lw=1.3, label='Pos. effect'),
        Line2D([0], [0], color=C_DEL,   lw=1.3, label='Del. effect'),
        Line2D([0], [0], color=C_MUTEX, lw=1.3, label='Mutex'),
    ]
    ax.legend(handles=legend, loc='lower center', fontsize=6.5,
              framealpha=0.88, ncol=8,
              bbox_to_anchor=(0.5, -0.075))


# ── Graph construction ────────────────────────────────────────────────────────

def build_graph(domain_file: str, problem_file: str,
                max_steps: int, debug: int) -> tuple:
    """Load PDDL and build the full planning graph (no early stop).

    Returns (graph, goal_time) where goal_time is the first layer at which
    all goals are reachable and non-mutex, or -1 if not reached.
    """
    graph = PlanningGraph()
    graph.debug_flag = debug
    graph.load(domain_file, problem_file)
    graph.process_data()
    # Build all layers so we can visualise the levelling behaviour too
    graph.create_graph(max_steps, auto_stop=False)

    goal_time = -1
    for t in range(max_steps + 1):
        if t < len(graph.fact_table) and graph.can_stop(t):
            goal_time = t
            break

    return graph, goal_time


# ── Entry point ───────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description='Visualise the BlackBox planning graph layer by layer',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument('-o', '--domain',      required=True)
    parser.add_argument('-f', '--problem',     required=True)
    parser.add_argument('--steps',            type=int, default=8,
                        help='Layers to build (default: 8)')
    parser.add_argument('--max-facts',        type=int, default=45,
                        help='Max fact nodes per column (default: 45)')
    parser.add_argument('--max-actions',      type=int, default=60,
                        help='Max action nodes per column (default: 60)')
    parser.add_argument('--no-noop',          action='store_true',
                        help='Hide NOOP actions')
    parser.add_argument('--save-all',         action='store_true',
                        help='Save every layer as a PNG and exit')
    parser.add_argument('--out-dir',          default='graphplan_viz',
                        help='Output directory for saved PNGs')
    parser.add_argument('--debug',            type=int, default=0)
    args = parser.parse_args()

    print(f'Loading {args.domain} + {args.problem}')
    graph, goal_time = build_graph(args.domain, args.problem,
                                   args.steps, args.debug)

    # Number of action layers with real content
    num_layers = min(args.steps, len(graph.op_table))
    if num_layers == 0:
        print('No layers built — try increasing --steps.')
        sys.exit(1)

    goal_names = {CONNECTOR.join(g) for g in graph.the_goals}
    gt_str = str(goal_time) if goal_time >= 0 else 'not reached'
    print(f'Graph: {num_layers} action layers  |  first goal-reachable layer: {gt_str}')
    if not args.save_all:
        print('Navigation: ← → arrows = prev/next layer  |  s = save PNG  |  q = quit')

    # ── Figure setup ──────────────────────────────────────────────────────
    fig, ax = plt.subplots(figsize=(21, 11))
    fig.patch.set_facecolor(C_BG)
    plt.subplots_adjust(left=0.005, right=0.995, top=0.915, bottom=0.065)

    state = {'t': 0}

    def _title(t: int) -> str:
        if goal_time >= 0 and t == goal_time:
            status = '✓  GOALS FIRST REACHABLE HERE'
        elif goal_time >= 0 and t > goal_time:
            status = '✓  goals reachable (levelled)'
        elif goal_time < 0:
            status = '✗  goals not reachable within built layers'
        else:
            status = '✗  goals not yet reachable'
        return (f'Planning Graph  —  Layer {t} / {num_layers - 1}'
                f'   |   {status}')

    def update(t: int):
        t = max(0, min(t, num_layers - 1))
        state['t'] = t
        render_layer(ax, graph, t, goal_names,
                     show_noop=not args.no_noop,
                     max_facts=args.max_facts,
                     max_actions=args.max_actions)
        fig.suptitle(_title(t), fontsize=11, fontweight='bold',
                     color='#1B2631', y=0.975)
        fig.canvas.draw_idle()

    def on_key(event):
        t = state['t']
        if   event.key in ('right', '.', '>'):  update(t + 1)
        elif event.key in ('left',  ',', '<'):  update(t - 1)
        elif event.key == 's':
            fname = f'layer_{t:02d}.png'
            fig.savefig(fname, dpi=150, bbox_inches='tight')
            print(f'Saved {fname}')
        elif event.key in ('q', 'escape'):
            plt.close('all')

    fig.canvas.mpl_connect('key_press_event', on_key)

    if args.save_all:
        os.makedirs(args.out_dir, exist_ok=True)
        for t in range(num_layers):
            update(t)
            fname = os.path.join(args.out_dir, f'layer_{t:02d}.png')
            fig.savefig(fname, dpi=150, bbox_inches='tight')
            print(f'Saved {fname}')
        print(f'All layers saved to  {args.out_dir}/')
        plt.close('all')
    else:
        update(0)
        plt.show()


if __name__ == '__main__':
    main()
