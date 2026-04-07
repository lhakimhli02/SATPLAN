#!/usr/bin/env python3
"""
visualize_graphplan_clustered.py  –  Predicate-clustered planning graph renderer.

Drop-in replacement for visualize_graphplan.render_layer().

Layout (single status board — no dual-grid, no edges):

  ┌─────────────────────────────────────────────┐
  │  on(x, y)  –  N×N reachability grid         │  ← top ~55 %
  ├──────────────┬──────────────┬───────────────┤
  │  clear(x)   │  ontable(x)  │  holding(x) + handempty  │  ← strips
  ├─────────────────────────────────────────────┤
  │  Real actions   (compact multi-column list) │  ← bottom ~20 %
  └─────────────────────────────────────────────┘

Colour key
  Blue   = fact reachable at this horizon
  Yellow = reachable goal fact
  Grey   = not yet reachable
  Red border = has at least one mutex partner

NOOPs are suppressed; only real actions are shown.

Usage (standalone):
    python visualize_graphplan_clustered.py -o domain.pddl -f problem.pddl [options]
"""

from __future__ import annotations

import sys
import os
import argparse

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.lines import Line2D

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from graphplan import PlanningGraph
from data_structures import CONNECTOR

# ── Colours ───────────────────────────────────────────────────────────────────
C_FACT   = '#AED6F1'   # blue  – reachable fact
C_GOAL   = '#F9E79F'   # yellow – reachable goal fact
C_ACTION = '#A9DFBF'   # green  – real action
C_NOOP   = '#D5D8DC'   # grey   – NOOP / empty cell
C_EMPTY  = '#EBEBEB'   # light grey – not yet reachable
C_MUTEX  = '#E74C3C'   # red border – has mutex
C_BG     = '#FAFAFA'
C_GRID   = '#CCCCCC'
C_LABEL  = '#1B2631'
C_DIM    = '#888888'


# ── Helpers ───────────────────────────────────────────────────────────────────

def _fact_pred_args(name: str) -> tuple[str, list[str]]:
    parts = name.split(CONNECTOR)
    return parts[0].lower(), [p.lower() for p in parts[1:]]


def _collect_blocks(fact_nodes) -> list[str]:
    blocks: set[str] = set()
    for f in fact_nodes:
        pred, args = _fact_pred_args(f.name)
        if pred in ('on', 'clear', 'ontable', 'holding') and args:
            blocks.update(args)
    return sorted(blocks)


def _action_short(name: str) -> str:
    """'stack_a_b' → 'stack(A,B)'"""
    low = name.lower()
    for prefix in ('pick-up', 'put-down', 'unstack', 'stack'):
        if low.startswith(prefix + CONNECTOR):
            rest = low[len(prefix) + 1:]
            args = rest.split(CONNECTOR)
            return f"{prefix}({','.join(a.upper() for a in args)})"
    parts = name.split(CONNECTOR)
    return f"{parts[0]}({','.join(p.upper() for p in parts[1:])})" if len(parts) > 1 else parts[0]


# ── Main render ───────────────────────────────────────────────────────────────

def render_layer(ax, graph: PlanningGraph, t: int,
                 goal_names: set, show_noop: bool,
                 max_facts: int, max_actions: int):
    """Single-panel predicate-clustered render of planning-graph layer t."""
    ax.clear()
    ax.set_xlim(0.0, 1.0)
    ax.set_ylim(0.0, 1.0)
    ax.axis('off')
    ax.set_facecolor(C_BG)

    # ── Collect nodes ──────────────────────────────────────────────────────
    all_ft  = list(graph.fact_table[t])
    all_ops = list(graph.op_table[t]) if t < len(graph.op_table) else []

    real_ops = [op for op in all_ops if not op.is_noop]
    noop_cnt = sum(1 for op in all_ops if op.is_noop)

    existing = {f.name: f for f in all_ft}
    blocks   = _collect_blocks(all_ft)
    n        = len(blocks)

    fm_total = sum(len(v.exclusive) for v in all_ft) // 2
    om_total = sum(len(op.exclusive) for op in all_ops) // 2

    # ── Layout constants ───────────────────────────────────────────────────
    PAD      = 0.03    # outer padding
    ROW_H    = 0.055   # height of clear/ontable/holding strips
    ACT_ZONE = 0.20    # fraction of height reserved for actions at bottom
    STRIP_Y0 = ACT_ZONE + 0.01
    STRIP_Y1 = STRIP_Y0 + ROW_H + 0.025 + ROW_H   # two strip rows
    GRID_Y0  = STRIP_Y1 + 0.025
    GRID_Y1  = 0.95

    GRID_X0  = PAD + 0.04   # leave room for row labels
    GRID_X1  = 1.0 - PAD

    # ── on(x,y) grid ──────────────────────────────────────────────────────
    ax.text(0.5, GRID_Y1 + 0.01,
            f'on( row↓ = block on top,  col→ = block below )   '
            f'[{t + 1 - 1} action layers built,  '
            f'{sum(1 for f in all_ft if _fact_pred_args(f.name)[0] == "on")} on-facts reachable]',
            ha='center', va='bottom', fontsize=6.5, fontweight='bold', color=C_LABEL)

    if n > 0:
        cell_w = (GRID_X1 - GRID_X0) / n
        cell_h = (GRID_Y1 - GRID_Y0) / n

        # Column headers
        for j, b in enumerate(blocks):
            cx = GRID_X0 + (j + 0.5) * cell_w
            ax.text(cx, GRID_Y1 + 0.003, b.upper(),
                    ha='center', va='bottom', fontsize=5.5, fontweight='bold',
                    color=C_LABEL)

        for i, b_row in enumerate(blocks):
            cy = GRID_Y1 - (i + 0.5) * cell_h
            # Row header
            ax.text(GRID_X0 - 0.004, cy, b_row.upper(),
                    ha='right', va='center', fontsize=5.5, fontweight='bold',
                    color=C_LABEL)

            for j, b_col in enumerate(blocks):
                cx = GRID_X0 + (j + 0.5) * cell_w
                pw = cell_w * 0.88
                ph = cell_h * 0.88

                if b_row == b_col:       # impossible: block on itself
                    ax.add_patch(mpatches.Rectangle(
                        (cx - pw / 2, cy - ph / 2), pw, ph,
                        facecolor='#DEDEDE', edgecolor='#BBBBBB',
                        linewidth=0.2, zorder=3))
                    continue

                fname  = CONNECTOR.join(['on', b_row, b_col])
                f_node = existing.get(fname)

                if f_node is not None:
                    is_goal   = fname in goal_names
                    face      = C_GOAL if is_goal else C_FACT
                    has_mutex = bool(f_node.exclusive)
                    ec, lw    = (C_MUTEX, 1.2) if has_mutex else (C_GRID, 0.3)
                else:
                    face, ec, lw = C_EMPTY, C_GRID, 0.15

                ax.add_patch(mpatches.Rectangle(
                    (cx - pw / 2, cy - ph / 2), pw, ph,
                    facecolor=face, edgecolor=ec, linewidth=lw, zorder=3))

    # ── Strip predicates ───────────────────────────────────────────────────
    # Row 1: clear  |  ontable      (left half / right half)
    # Row 2: holding  |  handempty  (left half / right half)
    strip_defs = [
        [('clear', 0.0, 0.5), ('ontable', 0.5, 1.0)],
        [('holding', 0.0, 0.5), ('handempty', 0.5, 1.0)],
    ]

    for row_idx, row_preds in enumerate(strip_defs):
        cy_centre = STRIP_Y0 + (1 - row_idx) * (ROW_H + 0.025) - ROW_H / 2

        for pred, xfrac0, xfrac1 in row_preds:
            x0s = PAD + xfrac0 * (1 - 2 * PAD)
            x1s = PAD + xfrac1 * (1 - 2 * PAD) - 0.005

            # Label
            ax.text((x0s + x1s) / 2, cy_centre + ROW_H / 2 + 0.004, pred,
                    ha='center', va='bottom', fontsize=5.5,
                    fontweight='bold', color=C_LABEL)

            if pred == 'handempty':
                fname  = 'handempty'
                f_node = existing.get(fname)
                cx     = (x0s + x1s) / 2
                hw     = min((x1s - x0s) * 0.35, 0.07)
                face, ec, lw = (
                    (C_GOAL if fname in goal_names else C_FACT,
                     C_MUTEX if f_node and f_node.exclusive else C_GRID,
                     0.8 if f_node and f_node.exclusive else 0.3)
                    if f_node is not None else (C_EMPTY, C_GRID, 0.15)
                )
                ax.add_patch(mpatches.Rectangle(
                    (cx - hw / 2, cy_centre - ROW_H * 0.43),
                    hw, ROW_H * 0.86,
                    facecolor=face, edgecolor=ec, linewidth=lw, zorder=3))
                ax.text(cx, cy_centre,
                        '✓' if f_node is not None else '',
                        ha='center', va='center', fontsize=7,
                        color='#1A5276', zorder=4)
            else:
                sw = (x1s - x0s) / max(n, 1)
                for j, b in enumerate(blocks):
                    cx    = x0s + (j + 0.5) * sw
                    fname = CONNECTOR.join([pred, b])
                    f_node = existing.get(fname)
                    if f_node is not None:
                        is_goal   = fname in goal_names
                        face      = C_GOAL if is_goal else C_FACT
                        has_mutex = bool(f_node.exclusive)
                        ec, lw    = (C_MUTEX, 0.8) if has_mutex else (C_GRID, 0.25)
                    else:
                        face, ec, lw = C_EMPTY, C_GRID, 0.15

                    ax.add_patch(mpatches.Rectangle(
                        (cx - sw * .43, cy_centre - ROW_H * .43),
                        sw * .86, ROW_H * .86,
                        facecolor=face, edgecolor=ec, linewidth=lw, zorder=3))
                    ax.text(cx, cy_centre, b.upper(),
                            ha='center', va='center', fontsize=4.5,
                            color='#333333', zorder=4)

    # ── Actions (compact multi-column list) ────────────────────────────────
    ax.axhline(ACT_ZONE - 0.005, color=C_GRID, linewidth=0.6, zorder=2)

    n_real = len(real_ops)
    ax.text(PAD, ACT_ZONE - 0.015,
            f'Real actions: {n_real}   NOOPs: {noop_cnt}   '
            f'Fact mutexes: {fm_total}   Action mutexes: {om_total}',
            ha='left', va='top', fontsize=5.5, color=C_DIM)

    if real_ops:
        labels   = [_action_short(op.name) for op in real_ops]
        n_cols   = max(1, min(6, n_real // 4 + 1))
        col_w    = (1.0 - 2 * PAD) / n_cols
        row_h_a  = (ACT_ZONE - 0.04) / max((n_real + n_cols - 1) // n_cols, 1)
        node_h   = min(row_h_a * 0.78, 0.022)

        for idx, (op, lbl) in enumerate(zip(real_ops, labels)):
            col  = idx % n_cols
            row  = idx // n_cols
            cx   = PAD + (col + 0.5) * col_w
            cy   = ACT_ZONE - 0.04 - row * row_h_a - row_h_a / 2

            has_mutex = bool(op.exclusive)
            ec = C_MUTEX if has_mutex else '#566573'
            lw = 0.8 if has_mutex else 0.4

            ax.add_patch(mpatches.FancyBboxPatch(
                (cx - col_w * 0.46, cy - node_h / 2),
                col_w * 0.92, node_h,
                boxstyle='round,pad=0.001',
                facecolor=C_ACTION, edgecolor=ec, linewidth=lw, zorder=3))

            chars = max(8, int(col_w * 130))
            ax.text(cx, cy,
                    lbl if len(lbl) <= chars else lbl[:chars - 2] + '..',
                    ha='center', va='center', fontsize=4.0,
                    fontfamily='monospace', color='#1A1A1A', zorder=4)

    # ── Legend ────────────────────────────────────────────────────────────
    legend = [
        mpatches.Patch(facecolor=C_FACT,   edgecolor=C_GRID,  label='Reachable fact'),
        mpatches.Patch(facecolor=C_GOAL,   edgecolor=C_GRID,  label='Reachable goal'),
        mpatches.Patch(facecolor=C_EMPTY,  edgecolor=C_GRID,  label='Not yet reachable'),
        mpatches.Patch(facecolor=C_ACTION, edgecolor='#566573', label='Real action'),
        mpatches.Patch(facecolor='white',  edgecolor=C_MUTEX,
                       linewidth=1.5, label='Has mutex'),
    ]
    ax.legend(handles=legend, loc='lower right', fontsize=5.5,
              framealpha=0.88, ncol=5,
              bbox_to_anchor=(1.0, 0.0))


# ── Standalone entry point ────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description='Clustered planning graph visualiser',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument('-o', '--domain',  required=True)
    parser.add_argument('-f', '--problem', required=True)
    parser.add_argument('--steps',        type=int, default=8)
    parser.add_argument('--max-facts',    type=int, default=200)
    parser.add_argument('--max-actions',  type=int, default=200)
    parser.add_argument('--no-noop',      action='store_true')
    parser.add_argument('--save-all',     action='store_true')
    parser.add_argument('--out-dir',      default='graphplan_clustered_viz')
    parser.add_argument('--debug',        type=int, default=0)
    args = parser.parse_args()

    print(f'Loading {args.domain} + {args.problem}')
    graph = PlanningGraph()
    graph.debug_flag = args.debug
    graph.load(args.domain, args.problem)
    graph.process_data()
    graph.create_graph(args.steps, auto_stop=False)

    goal_names_set = {CONNECTOR.join(g) for g in graph.the_goals}

    goal_time = -1
    for t in range(args.steps + 1):
        if t < len(graph.fact_table) and graph.can_stop(t):
            goal_time = t
            break

    num_layers = min(args.steps, len(graph.op_table))
    if num_layers == 0:
        print('No layers built.')
        return

    gt_str = str(goal_time) if goal_time >= 0 else 'not reached'
    print(f'Graph: {num_layers} action layers  |  first goal-reachable layer: {gt_str}')

    fig, ax = plt.subplots(figsize=(22, 11))
    fig.patch.set_facecolor(C_BG)
    plt.subplots_adjust(left=0.005, right=0.995, top=0.930, bottom=0.03)

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
        render_layer(ax, graph, t, goal_names_set,
                     show_noop=not args.no_noop,
                     max_facts=args.max_facts,
                     max_actions=args.max_actions)
        fig.suptitle(_title(t), fontsize=11, fontweight='bold',
                     color=C_LABEL, y=0.975)
        fig.canvas.draw_idle()

    def on_key(event):
        t = state['t']
        if   event.key in ('right', '.', '>'):  update(t + 1)
        elif event.key in ('left',  ',', '<'):  update(t - 1)
        elif event.key == 's':
            fname = f'clustered_layer_{t:02d}.png'
            fig.savefig(fname, dpi=150, bbox_inches='tight')
            print(f'Saved {fname}')
        elif event.key in ('q', 'escape'):
            plt.close('all')

    fig.canvas.mpl_connect('key_press_event', on_key)

    if args.save_all:
        os.makedirs(args.out_dir, exist_ok=True)
        for t in range(num_layers):
            update(t)
            fname = os.path.join(args.out_dir, f'clustered_layer_{t:02d}.png')
            fig.savefig(fname, dpi=150, bbox_inches='tight')
            print(f'Saved {fname}')
        print(f'All layers saved to {args.out_dir}/')
        plt.close('all')
    else:
        update(0)
        plt.show()


if __name__ == '__main__':
    main()
