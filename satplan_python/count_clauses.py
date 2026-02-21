"""
count_clauses.py - Print per-category CNF clause counts at each time horizon,
                   then solve and print the SAT solution and plan.

Usage:
    python count_clauses.py -o <domain.pddl> -f <problem.pddl> [-maxtime <n>]

Example:
    python count_clauses.py -o pddl_problems/domain.pddl -f pddl_problems/problem.pddl
"""
import argparse

from grounder import STRIPSProblem, ground_all_actions, collect_all_fluents
from strips_encoder import STRIPSEncoder
from sat_interface import IncrementalSATSolver
from data_structures import Sat, CONNECTOR


def main():
    parser = argparse.ArgumentParser(
        description='Count CNF clauses per category at each horizon, then solve'
    )
    parser.add_argument('-o', '--domain', required=True)
    parser.add_argument('-f', '--problem', required=True)
    parser.add_argument('-maxtime', type=int, default=10)
    parser.add_argument('-solver', default='cadical')
    parser.add_argument('-nomutex', action='store_true')
    parser.add_argument('-nocwa', action='store_true')
    args = parser.parse_args()

    # Load and ground once
    problem = STRIPSProblem()
    problem.load(args.domain, args.problem)
    problem.process_data()

    ground_actions = ground_all_actions(problem)
    all_fluents, initial_set, goal_literals = collect_all_fluents(problem, ground_actions)

    print(f"Ground actions: {len(ground_actions)}")
    print(f"Fluents:        {len(all_fluents)}")
    print()

    # One encoder and one solver session shared across all horizons
    enc = STRIPSEncoder(
        ground_actions, all_fluents, initial_set, goal_literals,
        close_world=not args.nocwa,
        emit_mutex=not args.nomutex,
    )
    session = IncrementalSATSolver(args.solver)

    for maxtime in range(1, args.maxtime + 1):
        # Count clauses per category using a scratch encoder at this horizon
        scratch = STRIPSEncoder(
            ground_actions, all_fluents, initial_set, goal_literals,
            close_world=not args.nocwa,
            emit_mutex=not args.nomutex,
        )
        scratch._ensure_vars_allocated(maxtime)

        def count(fn, *a, **kw):
            scratch.clauses = []
            fn(*a, **kw)
            return len(scratch.clauses)

        # For per-layer counts, only tally the last (new) layer
        t_last = maxtime - 1
        n_init  = count(scratch._generate_initial_state) if maxtime == 1 else 0
        n_goal  = count(scratch._generate_goal, maxtime)
        n_pre   = count(scratch._generate_preconditions, t_last)
        n_eff   = count(scratch._generate_effects, t_last)
        n_frame = count(scratch._generate_frame_axioms, t_last)
        n_mutex = count(scratch._generate_mutex, t_last) if not args.nomutex else 0
        new_layer = n_pre + n_eff + n_frame + n_mutex
        total_for_horizon = (n_init if maxtime == 1 else 0) + n_goal + new_layer

        print(f"Horizon t: {maxtime}  (+{new_layer} new layer clauses)")
        print(f"  Vars:          {scratch.numvar:>6,}")
        print(f"  New Clauses:   {total_for_horizon:>6,}")
        print(f"  Init (CWA):    {n_init:>6,}")
        print(f"  Goal:          {n_goal:>6,}")
        print(f"  Precond:       {n_pre:>6,}")
        print(f"  Effects:       {n_eff:>6,}")
        print(f"  Frame axioms:  {n_frame:>6,}")
        print(f"  Mutex AMO:     {n_mutex:>6,}")

        # Encode new layer onto shared encoder/session (incremental)
        new_clauses, numvar, _ = enc.encode(maxtime, incremental=True)
        if new_clauses:
            session.add_clauses(new_clauses)

        assumptions = enc.get_goal_assumptions()
        status, soln = session.solve(numvar=numvar, assumptions=assumptions)

        if status == Sat:
            plan = enc.extract_plan(soln, maxtime)
            action_count = sum(len(step) for step in plan)
            print(f"\n  Plan ({action_count} actions):")
            for t, step in enumerate(plan):
                for name in sorted(step):
                    parts = name.split(CONNECTOR)
                    print(f"    {t + 1}: ({' '.join(parts)})")
            print()
            break
        else:
            print(f"  UNSAT at this horizon\n")

    session.delete()


if __name__ == '__main__':
    main()
