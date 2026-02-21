"""
count_clauses.py - Print per-category CNF clause counts at each time horizon,
                   then solve and print the SAT solution and plan.

Usage:
    python count_clauses.py -o <domain.pddl> -f <problem.pddl> [-maxtime <n>]

Example:
    python count_clauses.py -o pddl_problems/domain.pddl -f pddl_problems/problem.pddl
"""
import argparse
import sys

from graphplan import PlanningGraph
from graph2wff import SATEncoder
from sat_interface import IncrementalSATSolver
from data_structures import Sat, CONNECTOR


def main():
    parser = argparse.ArgumentParser(description='Count CNF clauses per category at each time horizon, then solve')
    parser.add_argument('-o', '--domain', required=True)
    parser.add_argument('-f', '--problem', required=True)
    parser.add_argument('-maxtime', type=int, default=10)
    parser.add_argument('-axioms', type=int, default=7)
    parser.add_argument('-solver', default='cadical')
    args = parser.parse_args()

    for maxtime in range(1, args.maxtime + 1):
        graph = PlanningGraph()
        graph.load(args.domain, args.problem)
        graph.process_data()
        graph.create_graph(maxtime, auto_stop=False)

        num_goals = graph.setup_goals(maxtime)
        if num_goals == 0:
            continue

        enc = SATEncoder(graph, axioms=args.axioms)
        enc._remove_unneeded(maxtime)
        enc._assign_props(maxtime, num_goals, False, incremental=False)

        def count(fn, *a, **kw):
            enc.clauses = []
            fn(*a, **kw)
            return len(enc.clauses)

        n_init  = count(enc._generate_initial_state)
        n_goal  = count(enc._generate_goal_state, maxtime, num_goals)
        n_pre   = sum(count(enc._generate_precond, graph.op_table[t]) for t in range(maxtime))
        n_frame = sum(count(enc._generate_frame, graph.fact_table[t + 1], simplified=(t == maxtime - 1)) for t in range(maxtime))
        n_mutex = sum(count(enc._generate_op_mutex, graph.op_table[t], incremental=False) for t in range(maxtime))
        total   = n_init + n_goal + n_pre + n_frame + n_mutex

        print(f"Horizon t: {maxtime}")
        print(f"  Vars:          {enc.numvar:>6,}")
        print(f"  Total Clauses: {total:>6,}")
        print(f"  Init:          {n_init:>6,}")
        print(f"  Goal:          {n_goal:>6,}")
        print(f"  Precond:       {n_pre:>6,}")
        print(f"  Frame:         {n_frame:>6,}")
        print(f"  Mutex AMO:     {n_mutex:>6,}")

        # Re-encode fully to get the complete clause list, then solve
        clauses, numvar, numclause = enc.encode(maxtime, num_goals)

        session = IncrementalSATSolver(args.solver)
        session.add_clauses(clauses)
        status, soln = session.solve(numvar=numvar)
        session.delete()

        if status == Sat:
            enc.soln2graph(soln)
            print(f"\n  Plan:")
            action_count = 0
            for t in range(maxtime):
                for op in graph.op_table[t]:
                    if op.used and not op.is_noop:
                        parts = op.name.split(CONNECTOR)
                        print(f"    {t + 1}: ({' '.join(parts)})")
                        action_count += 1
            print(f"  {action_count} actions")
        else:
            print(f"\n  UNSAT at this horizon")

        print()


if __name__ == '__main__':
    main()
