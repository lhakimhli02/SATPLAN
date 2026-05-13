#!/usr/bin/env python3
"""
run_benchmarks.py - Benchmark runner for BlackBox vs SATplan comparison.

Measures wall-clock solve time and plan length across:
  - Planner: BlackBox (graph+SAT) vs SATplan (direct STRIPS→SAT)
  - Mutex: on vs off (SATplan only)
  - Step semantics: exists-step vs forall-step (SATplan only)
  - SAT mode: incremental vs non-incremental (both)
  - AMO encoding: ladder vs pairwise (SATplan only)
  - Problem difficulty: small / medium / hard

Usage:
    python benchmarks/run_benchmarks.py [--timeout 60] [--csv results.csv]
"""
from __future__ import annotations

import argparse
import csv
import os
import subprocess
import sys
import time

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))
BB_DIR  = os.path.join(REPO, 'Blackbox', 'blackbox_python')
SAT_DIR = os.path.join(REPO, 'satplan_python')
BM_DIR  = os.path.join(REPO, 'benchmarks')
DOMAIN  = os.path.join(BM_DIR, 'blocks_domain.pddl')

PROBLEMS = [
    ('S1', 'blocks_s1.pddl', 'small'),
    ('S2', 'blocks_s2.pddl', 'small'),
    ('M1', 'blocks_m1.pddl', 'medium'),
    ('M2', 'blocks_m2.pddl', 'medium'),
    ('H1', 'blocks_h1.pddl', 'hard'),
    ('H2', 'blocks_h2.pddl', 'hard'),
]

# Each config: (label, planner, extra_flags)
#   planner: 'blackbox' or 'satplan'
CONFIGS = [
    # ── BlackBox ─────────────────────────────────────────────────────────
    ('BB-default',        'blackbox', ['-noopt']),
    ('BB-noincsat',       'blackbox', ['-noopt', '-noincsat']),
    # ── SATplan: baseline ────────────────────────────────────────────────
    ('SP-default',        'satplan',  ['-noopt']),
    ('SP-noincsat',       'satplan',  ['-noopt', '-noincsat']),
    ('SP-nomutex',        'satplan',  ['-noopt', '-nomutex']),
    ('SP-forallstep',     'satplan',  ['-noopt', '-forallstep']),
    ('SP-pairwiseamo',    'satplan',  ['-noopt', '-pairwiseamo']),
    # ── SATplan: combo ───────────────────────────────────────────────────
    ('SP-forall+nomutex', 'satplan',  ['-noopt', '-forallstep', '-nomutex']),
]


def run_one(planner: str, flags: list[str], problem_file: str,
            timeout: int) -> dict:
    """
    Run one planner configuration on one problem.
    Returns {'status': 'sat'|'timeout'|'error', 'elapsed': float, 'plan_len': int}.
    """
    if planner == 'blackbox':
        cmd = [
            sys.executable, os.path.join(BB_DIR, 'blackbox.py'),
            '-o', DOMAIN, '-f', problem_file,
        ] + flags
        cwd = BB_DIR
    else:
        cmd = [
            sys.executable, os.path.join(SAT_DIR, 'satplan.py'),
            '-o', DOMAIN, '-f', problem_file,
        ] + flags
        cwd = SAT_DIR

    t0 = time.perf_counter()
    try:
        proc = subprocess.run(
            cmd, cwd=cwd,
            capture_output=True, text=True,
            timeout=timeout,
        )
        elapsed = time.perf_counter() - t0
        stdout = proc.stdout
        if proc.returncode != 0 and 'Sat' not in stdout and 'plan' not in stdout.lower():
            return {'status': 'error', 'elapsed': elapsed, 'plan_len': -1,
                    'stderr': proc.stderr[:200]}
        plan_len = _extract_plan_len(stdout)
        return {'status': 'sat', 'elapsed': elapsed, 'plan_len': plan_len}
    except subprocess.TimeoutExpired:
        return {'status': 'timeout', 'elapsed': timeout, 'plan_len': -1}
    except Exception as e:
        return {'status': 'error', 'elapsed': 0.0, 'plan_len': -1, 'stderr': str(e)}


def _extract_plan_len(stdout: str) -> int:
    """Parse plan length from planner stdout."""
    for line in stdout.splitlines():
        ll = line.lower().strip()
        # Both planners: "N actions in plan"
        if 'actions in plan' in ll:
            parts = line.split()
            for p in parts:
                if p.isdigit():
                    return int(p)
        # SATplan: "Plan length: N"
        if ll.startswith('plan length'):
            parts = line.split()
            for p in parts:
                if p.isdigit():
                    return int(p)
        # "Plan found at horizon N"
        if 'horizon' in ll and ('found' in ll or 'sat' in ll):
            parts = line.split()
            for p in parts:
                if p.isdigit():
                    return int(p)
    # Fallback: count action lines (lines starting with step number)
    actions = [l for l in stdout.splitlines()
               if l.strip() and l.strip()[0].isdigit() and ':' in l]
    return len(actions) if actions else -1


def main():
    parser = argparse.ArgumentParser(description='Benchmark runner')
    parser.add_argument('--timeout', type=int, default=60,
                        help='Per-run timeout in seconds (default: 60)')
    parser.add_argument('--csv', default=None,
                        help='Write results to CSV file')
    args = parser.parse_args()

    results = []
    header = ['config', 'planner', 'problem', 'difficulty',
              'status', 'elapsed_s', 'plan_len']

    print(f"{'Config':<22} {'Problem':<6} {'Diff':<7} {'Status':<9} "
          f"{'Time(s)':<9} {'PlanLen'}")
    print('-' * 65)

    for prob_id, prob_file, diff in PROBLEMS:
        problem_path = os.path.join(BM_DIR, prob_file)
        for cfg_label, planner, extra_flags in CONFIGS:
            r = run_one(planner, extra_flags, problem_path, args.timeout)
            elapsed = f'{r["elapsed"]:.3f}'
            plan_len = r['plan_len'] if r['plan_len'] >= 0 else '--'
            print(f'{cfg_label:<22} {prob_id:<6} {diff:<7} {r["status"]:<9} '
                  f'{elapsed:<9} {plan_len}')
            results.append([
                cfg_label, planner, prob_id, diff,
                r['status'], round(r['elapsed'], 4), r['plan_len'],
            ])

    print()

    if args.csv:
        with open(args.csv, 'w', newline='') as f:
            w = csv.writer(f)
            w.writerow(header)
            w.writerows(results)
        print(f'Results written to {args.csv}')

    return results


if __name__ == '__main__':
    main()
