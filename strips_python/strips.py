#!/usr/bin/env python3
"""
strips.py - CLI entry point for a plain STRIPS forward-search planner.

This is the classical approach: search the STRIPS state space directly
(states = sets of true fluents, actions = grounded STRIPS operators),
the way it's presented in Russell & Norvig / the AIMA "planning.py"
reference implementation (https://github.com/aimacode/aima-python).
No SAT encoding (SATplan) and no planning graph (BlackBox) — just
forward search from the initial state to a goal state.

Two search modes:
  * uninformed (--uninformed): breadth-first / uniform-cost search
    (all actions cost 1), guaranteed to return a shortest plan.
  * heuristic (default): greedy best-first search using the number of
    unsatisfied goal literals as a heuristic, which scales much better
    on larger problems at the cost of optimality.

Usage:
    python strips.py -o <domain.pddl> -f <problem.pddl> [options]
"""

from __future__ import annotations
import argparse
import heapq
import itertools
import os
import sys
import time as time_mod
from collections import deque

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                '..', 'satplan_python'))

from grounder import STRIPSProblem, ground_all_actions, collect_all_fluents, CONNECTOR


def _pretty_action(name: str) -> str:
    """Convert ``pick-up_c`` to ``(pick-up c)``."""
    parts = name.split(CONNECTOR)
    return '(' + ' '.join(parts) + ')'


def _goal_satisfied(state: frozenset, goal_literals: list[tuple[bool, str]]) -> bool:
    for polarity, fluent in goal_literals:
        if (fluent in state) != polarity:
            return False
    return True


def _goal_count(state: frozenset, goal_literals: list[tuple[bool, str]]) -> int:
    return sum(1 for polarity, fluent in goal_literals if (fluent in state) != polarity)


def _successors(state: frozenset, ground_actions):
    for ga in ground_actions:
        if ga.pos_pre <= state and not (ga.neg_pre & state):
            yield ga, (state - ga.del_eff) | ga.add_eff


def breadth_first_search(ground_actions, initial_set, goal_literals,
                         max_depth: int, node_limit: int):
    """Uninformed forward search (uniform-cost, since every action costs 1).
    Guaranteed to find a shortest plan (fewest actions) if one exists
    within max_depth."""
    start = frozenset(initial_set)
    if _goal_satisfied(start, goal_literals):
        return [], 0

    frontier = deque([(start, [])])
    visited = {start}
    expansions = 0

    while frontier:
        state, plan = frontier.popleft()
        if len(plan) >= max_depth:
            continue
        expansions += 1
        if expansions > node_limit:
            return None, expansions
        for ga, nstate in _successors(state, ground_actions):
            if nstate in visited:
                continue
            nplan = plan + [ga.name]
            if _goal_satisfied(nstate, goal_literals):
                return nplan, expansions
            visited.add(nstate)
            frontier.append((nstate, nplan))

    return None, expansions


def greedy_best_first_search(ground_actions, initial_set, goal_literals,
                             max_depth: int, node_limit: int):
    """Forward search guided by a goal-count heuristic: at each step,
    expand the state with the fewest unsatisfied goal literals first.
    Not guaranteed optimal, but scales much better than plain BFS."""
    start = frozenset(initial_set)
    if _goal_satisfied(start, goal_literals):
        return [], 0

    counter = itertools.count()
    h0 = _goal_count(start, goal_literals)
    frontier = [(h0, next(counter), start, [])]
    best_g = {start: 0}
    expansions = 0

    while frontier:
        _, _, state, plan = heapq.heappop(frontier)
        if best_g.get(state, -1) < len(plan):
            continue  # stale entry, a shorter path to this state was found
        if _goal_satisfied(state, goal_literals):
            return plan, expansions
        if len(plan) >= max_depth:
            continue
        expansions += 1
        if expansions > node_limit:
            return None, expansions
        for ga, nstate in _successors(state, ground_actions):
            ng = len(plan) + 1
            if nstate in best_g and best_g[nstate] <= ng:
                continue
            best_g[nstate] = ng
            nplan = plan + [ga.name]
            h = _goal_count(nstate, goal_literals)
            heapq.heappush(frontier, (ng + h, next(counter), nstate, nplan))

    return None, expansions


def main():
    parser = argparse.ArgumentParser(
        description='STRIPS - Plain forward state-space search planner '
                    '(AIMA-style; no SAT encoding, no planning graph)',
        add_help=False,
    )
    parser.add_argument('-o', '--domain', required=True, help='Domain PDDL file')
    parser.add_argument('-f', '--problem', required=True, help='Problem PDDL file')
    parser.add_argument('-g', '--output', default=None, help='Output plan file')
    parser.add_argument('-i', '--info', type=int, default=0, help='Debug info level (0-2)')
    parser.add_argument('-uninformed', action='store_true',
                        help='Use plain breadth-first search instead of the '
                             'goal-count greedy best-first search (slower, '
                             'but guarantees a shortest plan)')
    parser.add_argument('-maxdepth', type=int, default=60,
                        help='Max plan length to search for (default: 60)')
    parser.add_argument('-maxnodes', type=int, default=300000,
                        help='Max states to expand before giving up (default: 300000)')
    parser.add_argument('-norelevance', action='store_true',
                        help='Disable action relevance pruning during grounding')
    # Accepted for CLI compatibility with satplan.py/blackbox.py callers;
    # STRIPS forward search has no SAT solver to choose.
    parser.add_argument('-solver', nargs=argparse.REMAINDER, default=[])
    parser.add_argument('-noopt', action='store_true', help=argparse.SUPPRESS)
    parser.add_argument('-h', '--help', action='store_true', help='Show help')

    args = parser.parse_args()

    if args.help:
        _print_usage()
        sys.exit(0)

    debug = args.info
    global_start = time_mod.time()

    print("STRIPS (Python) - Plain forward state-space search")
    print(f"  Domain:  {args.domain}")
    print(f"  Problem: {args.problem}")
    print()

    problem = STRIPSProblem()
    problem.enable_relevance_pruning = not args.norelevance
    problem.debug = debug

    try:
        problem.load(args.domain, args.problem)
    except Exception as e:
        print(f"Error loading PDDL files: {e}", file=sys.stderr)
        sys.exit(1)

    t_pre = time_mod.time()
    problem.process_data()
    preprocess_sec = time_mod.time() - t_pre

    t_ground = time_mod.time()
    ground_actions = ground_all_actions(problem)
    ground_sec = time_mod.time() - t_ground

    if len(ground_actions) == 0:
        print("Error: no ground actions found", file=sys.stderr)
        sys.exit(1)

    all_fluents, initial_set, goal_literals = collect_all_fluents(problem, ground_actions)

    if len(goal_literals) == 0:
        print("Error: no goals specified", file=sys.stderr)
        sys.exit(1)

    if debug >= 1:
        print(f"  Ground actions: {len(ground_actions)}")
        print(f"  Fluents: {len(all_fluents)}")
        print(f"  Initial state: {len(initial_set)} true facts")
        print(f"  Goals: {len(goal_literals)}")
        print(f"  Grounding time: {ground_sec:.3f}s")
        print()

    search = breadth_first_search if args.uninformed else greedy_best_first_search
    mode = 'breadth-first' if args.uninformed else 'greedy best-first (goal-count heuristic)'
    if debug >= 1:
        print(f"Searching ({mode})...")

    t_search = time_mod.time()
    plan, expansions = search(ground_actions, initial_set, goal_literals,
                              args.maxdepth, args.maxnodes)
    search_sec = time_mod.time() - t_search

    print()
    print("Begin plan")
    if plan is None:
        print("End plan")
        print("0 actions in plan")
        print()
        print(f"No plan found (expanded {expansions} states, "
              f"limit depth={args.maxdepth} nodes={args.maxnodes})")
    else:
        for t, act_name in enumerate(plan):
            print(f"{t + 1}: {_pretty_action(act_name)}")
        print("End plan")
        print(f"{len(plan)} actions in plan")

        if args.output:
            with open(args.output, 'w') as fh:
                fh.write('\n'.join(_pretty_action(a) for a in plan) + '\n')

    elapsed = time_mod.time() - global_start
    print()
    if elapsed < 60:
        print(f"Total time: {elapsed:.2f} seconds")
    else:
        print(f"Total time: {elapsed / 60:.2f} minutes ({elapsed:.1f} seconds)")
    print("Timing breakdown:")
    print(f"  Preprocessing:  {preprocess_sec:.3f}s")
    print(f"  Grounding:      {ground_sec:.3f}s")
    print(f"  Search:         {search_sec:.3f}s ({expansions} states expanded, {mode})")


def _print_usage():
    print("""
STRIPS (Python) - Plain forward state-space search planner

Searches the STRIPS state space directly (states = sets of true
fluents), the classical approach described in Russell & Norvig and
implemented in AIMA's planning.py reference code
(https://github.com/aimacode/aima-python). No SAT encoding, no
planning graph.

Usage:
  python strips.py -o <domain.pddl> -f <problem.pddl> [options]

Required:
  -o <file>       Domain PDDL file
  -f <file>       Problem PDDL file

Options:
  -g <file>       Output plan file
  -i <level>      Debug level (0-2)
  -uninformed     Plain breadth-first search (guarantees a shortest
                  plan; slower on larger problems)
  -maxdepth <n>   Max plan length to search for (default: 60)
  -maxnodes <n>   Max states to expand before giving up (default: 300000)
  -norelevance    Disable action relevance pruning during grounding

Examples:
  python strips.py -o domain.pddl -f problem.pddl
  python strips.py -o domain.pddl -f problem.pddl -uninformed
  python strips.py -o domain.pddl -f problem.pddl -maxnodes 1000000
""")


if __name__ == '__main__':
    main()
