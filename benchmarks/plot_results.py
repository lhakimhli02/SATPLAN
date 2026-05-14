#!/usr/bin/env python3
"""
plot_results.py - Bar chart visualizations of benchmark results.

Generates four charts:
  1. Solve time by config, grouped by problem (all 6 problems, side-by-side bars)
  2. Solve time on the hardest problem (H1) — most informative single comparison
  3. Plan length by config across all problems — shows quality impact of flags
  4. Incremental vs non-incremental speedup factor per problem

Usage:
    python benchmarks/plot_results.py [--csv benchmarks/results.csv] [--out benchmarks/]
"""
from __future__ import annotations

import argparse
import csv
import os
from collections import defaultdict

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import numpy as np

# ── Colour palette ────────────────────────────────────────────────────────────

COLORS = {
    'BB-default':        '#2196F3',   # blue
    'BB-noincsat':       '#64B5F6',   # light blue
    'SP-default':        '#4CAF50',   # green
    'SP-noincsat':       '#A5D6A7',   # light green
    'SP-nomutex':        '#F44336',   # red
    'SP-forallstep':     '#FF9800',   # orange
    'SP-pairwiseamo':    '#9C27B0',   # purple
    'SP-forall+nomutex': '#FFCDD2',   # pale red
}

CONFIG_ORDER = [
    'BB-default', 'BB-noincsat',
    'SP-default', 'SP-noincsat',
    'SP-forallstep', 'SP-pairwiseamo',
]

PROBLEM_ORDER = ['S1', 'S2', 'M1', 'M2', 'H1', 'H2']
XL_ORDER      = ['XL1', 'XL2']
DEPOT_ORDER   = ['D1', 'D2']
DIFF_LABEL = {'S1': 'S1\n(small)', 'S2': 'S2\n(small)',
              'M1': 'M1\n(medium)', 'M2': 'M2\n(medium)',
              'H1': 'H1\n(hard)',   'H2': 'H2\n(hard)',
              'XL1': 'XL1\nFerry\n(8 cars)', 'XL2': 'XL2\nHanoi\n(5 discs)',
              'D1': 'D1\nDepot\n(2 crates)', 'D2': 'D2\nDepot\n(3 crates)'}


def load_csv(path: str) -> list[dict]:
    with open(path) as f:
        return list(csv.DictReader(f))


def pivot(rows: list[dict], metric: str) -> dict[str, dict[str, float]]:
    """Returns data[config][problem] = value."""
    data: dict[str, dict[str, float]] = defaultdict(dict)
    for r in rows:
        data[r['config']][r['problem']] = float(r[metric])
    return data


# ── Chart 1: solve time grouped by problem ────────────────────────────────────

def plot_time_by_problem(rows, out_dir):
    data = pivot(rows, 'elapsed_s')
    n_configs = len(CONFIG_ORDER)
    n_probs   = len(PROBLEM_ORDER)
    width     = 0.09
    x         = np.arange(n_probs)

    fig, ax = plt.subplots(figsize=(14, 5))

    offsets = np.linspace(-(n_configs - 1) / 2, (n_configs - 1) / 2, n_configs) * width

    for i, cfg in enumerate(CONFIG_ORDER):
        vals = [data[cfg].get(p, 0) for p in PROBLEM_ORDER]
        ax.bar(x + offsets[i], vals, width, label=cfg,
               color=COLORS[cfg], edgecolor='white', linewidth=0.4)

    ax.set_xlabel('Problem', fontsize=11)
    ax.set_ylabel('Solve time (s)', fontsize=11)
    ax.set_title('Solve Time by Problem and Configuration', fontsize=13, fontweight='bold')
    ax.set_xticks(x)
    ax.set_xticklabels([DIFF_LABEL[p] for p in PROBLEM_ORDER], fontsize=9)
    ax.legend(ncol=4, fontsize=8, loc='upper left')
    ax.set_ylim(bottom=0)
    ax.yaxis.grid(True, linestyle='--', alpha=0.5)
    ax.set_axisbelow(True)
    fig.tight_layout()

    path = os.path.join(out_dir, 'chart_time_by_problem.png')
    fig.savefig(path, dpi=150)
    plt.close(fig)
    print(f'Saved {path}')


# ── Chart 2: solve time on H1 (hardest problem) ───────────────────────────────

def plot_time_h1(rows, out_dir):
    data = pivot(rows, 'elapsed_s')
    configs = CONFIG_ORDER
    vals    = [data[c].get('H1', 0) for c in configs]

    fig, ax = plt.subplots(figsize=(10, 4.5))
    bars = ax.bar(configs, vals, color=[COLORS[c] for c in configs],
                  edgecolor='white', linewidth=0.5)

    # Value labels on bars
    for bar, v in zip(bars, vals):
        ax.text(bar.get_x() + bar.get_width() / 2, bar.get_height() + 0.02,
                f'{v:.3f}s', ha='center', va='bottom', fontsize=8)

    ax.set_ylabel('Solve time (s)', fontsize=11)
    ax.set_title('Solve Time on H1 (7-block tower, hardest)', fontsize=13, fontweight='bold')
    ax.set_xticklabels(configs, rotation=25, ha='right', fontsize=9)
    ax.yaxis.grid(True, linestyle='--', alpha=0.5)
    ax.set_axisbelow(True)
    ax.set_ylim(bottom=0, top=max(vals) * 1.2)

    # Separator line between BB and SP
    ax.axvline(x=1.5, color='gray', linestyle=':', linewidth=1.2)
    ax.text(0.5, max(vals) * 1.12, 'BlackBox', ha='center', fontsize=9, color='#2196F3')
    ax.text(5.0, max(vals) * 1.12, 'SATplan', ha='center', fontsize=9, color='#4CAF50')

    fig.tight_layout()
    path = os.path.join(out_dir, 'chart_time_h1.png')
    fig.savefig(path, dpi=150)
    plt.close(fig)
    print(f'Saved {path}')


# ── Chart 3: plan length across problems ─────────────────────────────────────

def plot_plan_length(rows, out_dir):
    data = pivot(rows, 'plan_len')
    n_configs = len(CONFIG_ORDER)
    n_probs   = len(PROBLEM_ORDER)
    width     = 0.09
    x         = np.arange(n_probs)

    fig, ax = plt.subplots(figsize=(14, 5))
    offsets = np.linspace(-(n_configs - 1) / 2, (n_configs - 1) / 2, n_configs) * width

    for i, cfg in enumerate(CONFIG_ORDER):
        vals = [data[cfg].get(p, 0) for p in PROBLEM_ORDER]
        ax.bar(x + offsets[i], vals, width, label=cfg,
               color=COLORS[cfg], edgecolor='white', linewidth=0.4)

    ax.set_xlabel('Problem', fontsize=11)
    ax.set_ylabel('Plan length (actions)', fontsize=11)
    ax.set_title('Plan Length by Problem and Configuration', fontsize=13, fontweight='bold')
    ax.set_xticks(x)
    ax.set_xticklabels([DIFF_LABEL[p] for p in PROBLEM_ORDER], fontsize=9)
    ax.legend(ncol=4, fontsize=8, loc='upper left')
    ax.set_ylim(bottom=0)
    ax.yaxis.grid(True, linestyle='--', alpha=0.5)
    ax.set_axisbelow(True)
    fig.tight_layout()

    path = os.path.join(out_dir, 'chart_plan_length.png')
    fig.savefig(path, dpi=150)
    plt.close(fig)
    print(f'Saved {path}')


# ── Chart 4: incremental vs non-incremental speedup ──────────────────────────

def plot_incremental_speedup(rows, out_dir):
    data = pivot(rows, 'elapsed_s')
    problems = PROBLEM_ORDER

    bb_speedup  = [data['BB-noincsat'].get(p, 1) / max(data['BB-default'].get(p, 1), 1e-6)
                   for p in problems]
    sp_speedup  = [data['SP-noincsat'].get(p, 1) / max(data['SP-default'].get(p, 1), 1e-6)
                   for p in problems]

    x = np.arange(len(problems))
    width = 0.3

    fig, ax = plt.subplots(figsize=(9, 4.5))
    b1 = ax.bar(x - width / 2, bb_speedup, width, label='BlackBox',
                color='#2196F3', edgecolor='white')
    b2 = ax.bar(x + width / 2, sp_speedup, width, label='SATplan',
                color='#4CAF50', edgecolor='white')

    # Reference line at 1.0 (no speedup)
    ax.axhline(1.0, color='black', linewidth=1, linestyle='--', label='no speedup (1.0×)')

    # Value labels
    for bar in list(b1) + list(b2):
        h = bar.get_height()
        ax.text(bar.get_x() + bar.get_width() / 2, h + 0.03,
                f'{h:.2f}×', ha='center', va='bottom', fontsize=8)

    ax.set_xlabel('Problem', fontsize=11)
    ax.set_ylabel('Speedup factor\n(non-incremental ÷ incremental time)', fontsize=10)
    ax.set_title('Incremental SAT Speedup Factor\n(higher = incremental is faster)',
                 fontsize=12, fontweight='bold')
    ax.set_xticks(x)
    ax.set_xticklabels([DIFF_LABEL[p] for p in problems], fontsize=9)
    ax.legend(fontsize=9)
    ax.yaxis.grid(True, linestyle='--', alpha=0.5)
    ax.set_axisbelow(True)
    ax.set_ylim(bottom=0)
    fig.tight_layout()

    path = os.path.join(out_dir, 'chart_incremental_speedup.png')
    fig.savefig(path, dpi=150)
    plt.close(fig)
    print(f'Saved {path}')


# ── Chart 5: XL problems — solve time by config ──────────────────────────────

def plot_xl_time(rows, out_dir):
    """Bar chart of solve time on XL1 (Ferry) and XL2 (Hanoi) per config."""
    data = pivot(rows, 'elapsed_s')
    TIMEOUT = 120.0

    fig, axes = plt.subplots(1, 2, figsize=(13, 5), sharey=False)
    titles = {'XL1': 'XL1 — Ferry (8 cars, 31 steps)',
              'XL2': 'XL2 — Hanoi 5 discs (31 steps)'}

    for ax, prob in zip(axes, XL_ORDER):
        vals  = [data[c].get(prob, TIMEOUT) for c in CONFIG_ORDER]
        colors = [COLORS[c] for c in CONFIG_ORDER]
        # Mark timeouts differently
        bar_vals = [min(v, TIMEOUT) for v in vals]
        bars = ax.bar(CONFIG_ORDER, bar_vals, color=colors, edgecolor='white', linewidth=0.5)

        for bar, v, cfg in zip(bars, vals, CONFIG_ORDER):
            label = 'T/O' if v >= TIMEOUT else f'{v:.2f}s'
            color = 'red' if v >= TIMEOUT else 'black'
            ax.text(bar.get_x() + bar.get_width() / 2,
                    bar.get_height() + max(bar_vals) * 0.02,
                    label, ha='center', va='bottom', fontsize=7, color=color,
                    fontweight='bold' if v >= TIMEOUT else 'normal')

        # Dashed line at timeout ceiling
        ax.axhline(TIMEOUT, color='red', linestyle='--', linewidth=1, alpha=0.5,
                   label='120 s timeout')
        ax.set_title(titles[prob], fontsize=11, fontweight='bold')
        ax.set_ylabel('Solve time (s)', fontsize=10)
        ax.set_xticklabels(CONFIG_ORDER, rotation=30, ha='right', fontsize=8)
        ax.yaxis.grid(True, linestyle='--', alpha=0.4)
        ax.set_axisbelow(True)
        ax.set_ylim(bottom=0, top=TIMEOUT * 1.18)

        # BB / SP divider
        ax.axvline(x=1.5, color='gray', linestyle=':', linewidth=1)
        ax.text(0.5, TIMEOUT * 1.10, 'BlackBox', ha='center', fontsize=8, color='#2196F3')
        ax.text(5.0, TIMEOUT * 1.10, 'SATplan',  ha='center', fontsize=8, color='#4CAF50')

    fig.tight_layout()
    path = os.path.join(out_dir, 'chart_xl_time.png')
    fig.savefig(path, dpi=150)
    plt.close(fig)
    print(f'Saved {path}')


# ── Chart 6: Depot problems — solve time by config ───────────────────────────

def plot_depot_time(rows, out_dir):
    """Bar chart of solve time on D1 and D2 (depot domain) per config."""
    data = pivot(rows, 'elapsed_s')
    TIMEOUT = 120.0

    titles = {'D1': 'D1 — Depot small (2 crates, ~9 steps)',
              'D2': 'D2 — Depot medium (3 crates, ~13 steps)'}

    # skip if depot data not present
    if not any(data[c].get('D1') or data[c].get('D2') for c in CONFIG_ORDER):
        return

    fig, axes = plt.subplots(1, 2, figsize=(13, 5), sharey=False)
    for ax, prob in zip(axes, DEPOT_ORDER):
        vals     = [data[c].get(prob, TIMEOUT) for c in CONFIG_ORDER]
        bar_vals = [min(v, TIMEOUT) for v in vals]
        max_val  = max(bar_vals) if max(bar_vals) > 0 else 1.0
        bars = ax.bar(CONFIG_ORDER, bar_vals,
                      color=[COLORS[c] for c in CONFIG_ORDER],
                      edgecolor='white', linewidth=0.5)

        for bar, v in zip(bars, vals):
            label = 'T/O' if v >= TIMEOUT else f'{v:.3f}s'
            color = 'red' if v >= TIMEOUT else 'black'
            ax.text(bar.get_x() + bar.get_width() / 2,
                    bar.get_height() + max_val * 0.03,
                    label, ha='center', va='bottom', fontsize=7, color=color,
                    fontweight='bold' if v >= TIMEOUT else 'normal')

        ax.set_title(titles[prob], fontsize=11, fontweight='bold')
        ax.set_ylabel('Solve time (s)', fontsize=10)
        ax.set_xticklabels(CONFIG_ORDER, rotation=30, ha='right', fontsize=8)
        ax.yaxis.grid(True, linestyle='--', alpha=0.4)
        ax.set_axisbelow(True)
        ax.set_ylim(bottom=0, top=max_val * 1.25)

        ax.axvline(x=1.5, color='gray', linestyle=':', linewidth=1)
        ax.text(0.5, max_val * 1.15, 'BlackBox', ha='center', fontsize=8, color='#2196F3')
        ax.text(5.0, max_val * 1.15, 'SATplan',  ha='center', fontsize=8, color='#4CAF50')

    fig.tight_layout()
    path = os.path.join(out_dir, 'chart_depot_time.png')
    fig.savefig(path, dpi=150)
    plt.close(fig)
    print(f'Saved {path}')


# ── Entry point ───────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--csv', default='benchmarks/results.csv')
    parser.add_argument('--out', default='benchmarks/')
    args = parser.parse_args()

    rows = load_csv(args.csv)
    os.makedirs(args.out, exist_ok=True)

    plot_time_by_problem(rows, args.out)
    plot_time_h1(rows, args.out)
    plot_plan_length(rows, args.out)
    plot_depot_time(rows, args.out)

    print('\nAll charts saved.')


if __name__ == '__main__':
    main()
