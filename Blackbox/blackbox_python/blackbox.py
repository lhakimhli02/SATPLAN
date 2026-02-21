#!/usr/bin/env python3
"""
blackbox.py - CLI entry point for BlackBox SATPLAN.

Replaces: main() in graphplan.cpp

Usage:
    python blackbox.py -o <domain.pddl> -f <problem.pddl> [options]
"""

from __future__ import annotations
import argparse
import sys
import time as time_mod

from data_structures import (
    SolverSpec, Graphplan_Solver, Anysat,
    Sat, Unsat, Timeout, Failure,
    PrintLit, PrintCNF, PrintModel,
)
from graphplan import PlanningGraph
from planner import Planner


def parse_solver_args(args: list[str]) -> list[SolverSpec]:
    """Parse the solver specification from the command line.

    Supports:  ``-solver {-maxsec N} <name> {-then {-maxsec N} <name> ...}``

    Returns a list of SolverSpec.
    """
    if not args:
        # Default to SAT-first (matches classic BlackBox behavior of using
        # an external SAT solver by default rather than unbounded GraphPlan).
        return [SolverSpec(solver_name='cadical', solver_type=Anysat)]

    specs: list[SolverSpec] = []
    i = 0
    cur_maxsec = 0
    cur_maxit = 0
    cur_argv: list[str] = []

    while i < len(args):
        tok = args[i]
        if tok == '-then':
            i += 1
            cur_maxsec = 0
            cur_maxit = 0
            cur_argv = []
            continue
        elif tok == '-maxsec':
            i += 1
            if i < len(args):
                cur_maxsec = int(args[i])
            i += 1
            continue
        elif tok == '-maxit':
            i += 1
            if i < len(args):
                cur_maxit = int(args[i])
            i += 1
            continue
        else:
            # This is a solver name
            solver_name = tok
            solver_type = Anysat
            if solver_name == 'graphplan':
                solver_type = Graphplan_Solver

            spec = SolverSpec(
                solver_name=solver_name,
                solver_type=solver_type,
                maxsec=cur_maxsec,
                maxit=cur_maxit,
                argv=list(cur_argv),
            )
            specs.append(spec)
            cur_maxsec = 0
            cur_maxit = 0
            cur_argv = []
            i += 1
            continue

    if not specs:
        specs.append(SolverSpec(solver_name='cadical',
                                solver_type=Anysat))
    return specs


def main():
    parser = argparse.ArgumentParser(
        description='BlackBox SATPLAN - SAT-based planning system',
        add_help=False,
    )
    parser.add_argument('-o', '--domain', required=True,
                        help='Domain PDDL file')
    parser.add_argument('-f', '--problem', required=True,
                        help='Problem PDDL file')
    parser.add_argument('-g', '--output', default=None,
                        help='Output plan file')
    parser.add_argument('-t', '--time', type=int, default=0,
                        help='Fixed plan length (0 = auto)')
    parser.add_argument('-i', '--info', type=int, default=0,
                        help='Debug info level (0-2)')
    parser.add_argument('-n', '--forceneg', action='store_true',
                        help='Force negative facts')
    parser.add_argument('-step', type=int, default=1,
                        help='Graph increment step size')
    parser.add_argument('-noskip', action='store_true',
                        help="Don't skip graphplan")
    parser.add_argument('-noopt', action='store_true',
                        help='Stop at first solution')
    parser.add_argument('-noincsat', action='store_true',
                        help='Disable incremental SAT across horizons')
    parser.add_argument('-norelevance', action='store_true',
                        help='Disable action/schema relevance pruning')
    parser.add_argument('-printlit', action='store_true',
                        help='Print WFF literals')
    parser.add_argument('-printcnf', action='store_true',
                        help='Print DIMACS CNF')
    parser.add_argument('-axioms', type=int, default=7,
                        help='Encoding preset (7,15,31,63,129)')
    parser.add_argument('-M', type=int, default=2048,
                        help='Max nodes per layer')
    parser.add_argument('-maxfail', type=int, default=0,
                        help='Max solver failures (0=unlimited)')
    parser.add_argument('-maxauto', type=int, default=100,
                        help='Max auto plan length')
    parser.add_argument('-maxglobalsec', type=int, default=0,
                        help='Global time limit in seconds')
    parser.add_argument('-solver', nargs=argparse.REMAINDER, default=[],
                        help='Solver specification')
    parser.add_argument('-h', '--help', action='store_true',
                        help='Show help')

    args = parser.parse_args()

    if args.help:
        _print_usage()
        sys.exit(0)

    domain_file = args.domain
    problem_file = args.problem
    output_file = args.output
    fixed_time = args.time
    debug = args.info
    step_size = args.step
    axioms = args.axioms
    max_auto = args.maxauto
    max_fail = args.maxfail
    max_global_sec = args.maxglobalsec

    # Parse solver specs
    solver_specs = parse_solver_args(args.solver)

    global_start = time_mod.time()

    # ── 1. Load domain and problem ──────────────────────────────────────

    print(f"BlackBox SATPLAN (Python)")
    print(f"  Domain:  {domain_file}")
    print(f"  Problem: {problem_file}")
    print()

    graph = PlanningGraph()
    graph.debug_flag = debug
    graph.force_neg_flag = args.forceneg
    graph.maxnodes = args.M
    graph.enable_relevance_pruning = not args.norelevance
    graph_build_sec_total = 0.0

    try:
        graph.load(domain_file, problem_file)
    except Exception as e:
        print(f"Error loading PDDL files: {e}", file=sys.stderr)
        sys.exit(1)

    if debug >= 1:
        print(f"  Domain: {graph.domain_name}")
        print(f"  Problem: {graph.problem_name}")
        print(f"  Operators: {len(graph.ops)}")
        print(f"  Objects: {len(graph.objects)}")
        print(f"  Initial facts: {len(graph.initial_facts)}")
        print(f"  Goals: {len(graph.the_goals)}")
        print()

    # ── 2. Process data ─────────────────────────────────────────────────

    graph.process_data()

    if debug >= 2:
        print("=== Parsed PDDL ===")
        print(f"Action schemas ({len(graph.ops)}):")
        for op in graph.ops:
            params_str = ' '.join(op.params)
            print(f"  ({op.name} {params_str})")
            print(f"    Pre:  {op.preconds}")
            print(f"    Eff:  {op.effects}")
        print(f"\nObjects ({len(graph.objects)}): {' '.join(graph.objects)}")
        print(f"\nInitial facts ({len(graph.initial_facts)}):")
        for fact in graph.initial_facts:
            print(f"  ({' '.join(fact)})")
        print(f"\nGoals ({len(graph.the_goals)}):")
        for goal in graph.the_goals:
            print(f"  ({' '.join(goal)})")
        print()

    num_goals = len(graph.the_goals)
    if num_goals == 0:
        print("Error: no goals specified", file=sys.stderr)
        sys.exit(1)

    # ── 3. Create initial planning graph ────────────────────────────────

    if fixed_time > 0:
        max_time = fixed_time
    else:
        max_time = max_auto

    if debug >= 1:
        print(f"  Building planning graph (max_time={max_time})...")

    t_graph_build = time_mod.time()
    graph_time = graph.create_graph(max_time, auto_stop=(fixed_time == 0))
    graph_build_sec_total += (time_mod.time() - t_graph_build)

    if graph_time < 0 and fixed_time > 0:
        print("Problem unsolvable: goals unreachable or mutually exclusive")
        sys.exit(1)

    if debug >= 1:
        if graph_time >= 0:
            print(f"  Graph built to time {graph_time}")
        else:
            print(f"  Graph levelled without reaching goals")
        print()

    # ── 4. Search for plan ──────────────────────────────────────────────

    printflag = 0
    if args.printlit:
        printflag |= PrintLit | PrintModel
    if args.printcnf:
        printflag |= PrintCNF | PrintModel

    planner = Planner(
        graph=graph,
        solver_specs=solver_specs,
        axioms=axioms,
        printflag=printflag,
        debug=debug,
        noopt=args.noopt,
        noskip=args.noskip,
        incremental_sat=not args.noincsat,
    )

    if fixed_time > 0:
        # Fixed time: solve at exactly this time
        if graph_time < 0:
            print("Problem unsolvable at this time step")
            sys.exit(1)
        result = planner.do_plan(fixed_time)
        if result == Sat:
            planner.print_plan(fixed_time, output_file)
        else:
            print(f"No plan found at time {fixed_time}")
    else:
        # Auto mode: iteratively increase time
        start_t = max(1, graph_time) if graph_time > 0 else 1
        found = False
        fail_count = 0
        cur_time = start_t

        while cur_time <= max_time:
            # Check global timeout
            if max_global_sec > 0:
                if time_mod.time() - global_start > max_global_sec:
                    print("Global time limit reached")
                    break

            # Ensure graph is built to this time
            if graph_time < cur_time:
                t_graph_extend = time_mod.time()
                graph_time = graph.extend_graph(graph_time if graph_time >= 0 else 0,
                                                cur_time)
                graph_build_sec_total += (time_mod.time() - t_graph_extend)

            if not graph.can_stop(cur_time):
                cur_time += step_size
                continue

            if debug >= 1:
                print(f"Trying plan length {cur_time}...")

            result = planner.do_plan(cur_time)

            if result == Sat:
                # Minimize actions at the current makespan using a fresh
                # solver with cardinality constraints.
                num_goals = graph.setup_goals(cur_time)
                best_count = planner.minimize_plan_actions(cur_time, num_goals)
                best_time = cur_time
                best_snapshot = planner._snapshot_plan_usage(cur_time)
                if debug >= 1:
                    print(f"  Optimized to {best_count} actions at makespan {cur_time}")

                # Search longer makespans — a less parallel plan may use
                # fewer total actions.
                stall = 0
                for extra in range(1, best_count):
                    ext_time = cur_time + extra
                    if ext_time > max_time:
                        break
                    if graph_time < ext_time:
                        t_ext = time_mod.time()
                        graph_time = graph.extend_graph(graph_time, ext_time)
                        graph_build_sec_total += (time_mod.time() - t_ext)
                    if not graph.can_stop(ext_time):
                        continue
                    num_goals = graph.setup_goals(ext_time)
                    ext_count = planner.minimize_plan_actions(ext_time, num_goals)
                    if ext_count < 0:
                        continue  # UNSAT at this makespan
                    if debug >= 1:
                        print(f"  Makespan {ext_time}: {ext_count} actions")
                    if ext_count < best_count:
                        best_count = ext_count
                        best_time = ext_time
                        best_snapshot = planner._snapshot_plan_usage(ext_time)
                        stall = 0
                    else:
                        stall += 1
                        if stall >= 3:
                            break  # no improvement for 3 consecutive makespans

                planner._restore_plan_usage(best_time, best_snapshot)
                planner.plan_time = best_time
                planner.print_plan(best_time, output_file)
                found = True
                break
            elif result == Unsat:
                if debug >= 1:
                    print(f"  No plan at time {cur_time}")
            elif result == Timeout:
                fail_count += 1
                if max_fail > 0 and fail_count >= max_fail:
                    print(f"Max failures ({max_fail}) reached")
                    break
            else:
                fail_count += 1
                if max_fail > 0 and fail_count >= max_fail:
                    break

            cur_time += step_size

        if not found:
            if cur_time > max_time:
                print(f"No plan found up to time {max_time}")

    # ── 5. Print timing ────────────────────────────────────────────────

    elapsed = time_mod.time() - global_start
    print()
    if elapsed < 60:
        print(f"Total time: {elapsed:.2f} seconds")
    else:
        print(f"Total time: {elapsed / 60:.2f} minutes ({elapsed:.1f} seconds)")
    timing = planner.get_timing_stats()
    sat_encode_sec = float(timing['sat_encode_sec'])
    sat_solve_sec = float(timing['sat_solve_sec'])
    sat_calls = int(timing['sat_calls'])
    other_sec = max(0.0, elapsed - graph_build_sec_total - sat_encode_sec - sat_solve_sec)
    print("Timing breakdown:")
    print(f"  Graph construction: {graph_build_sec_total:.2f}s")
    print(f"  CNF generation:     {sat_encode_sec:.2f}s")
    print(f"  SAT solve:          {sat_solve_sec:.2f}s ({sat_calls} calls)")
    print(f"  Other overhead:     {other_sec:.2f}s")


def _print_usage():
    print("""
BlackBox SATPLAN (Python rewrite)

Usage:
  python blackbox.py -o <domain.pddl> -f <problem.pddl> [options]

Required:
  -o <file>         Domain PDDL file
  -f <file>         Problem PDDL file

Options:
  -g <file>         Output plan file
  -t <int>          Fixed plan length (0 = auto)
  -i <level>        Debug info level (0-2)
  -n                Force negative facts
  -step <n>         Graph increment step size (default: 1)
  -noskip           Don't skip graphplan
  -noopt            Stop at first solution
  -noincsat         Disable incremental SAT across horizons
  -norelevance      Disable action/schema relevance pruning
  -printlit         Print WFF literals
  -printcnf         Print DIMACS CNF
  -axioms <type>    Encoding preset: 7 (default), 15, 31, 63, 129
  -M <int>          Max nodes per layer (default: 2048)
  -maxfail <n>      Max solver failures (0=unlimited)
  -maxauto <n>      Max auto plan length (default: 100)
  -maxglobalsec <n> Global time limitclaud in seconds

Solver specification:
  -solver {-maxsec N} <solver> {-then {-maxsec N} <solver> ...}

  Available solvers:
    cadical     CaDiCaL 1.9.5 (default solver, via PySAT)
    graphplan   Built-in backward-chaining search
    glucose     Glucose 4.2 (via PySAT, strong on industrial benchmarks)
    maple       MapleChrono (via PySAT, SAT competition 2018 winner)
    minisat     MiniSat (via PySAT, classic CDCL solver)
    kissat      Kissat (external binary, state-of-the-art)
    walksat     WalkSAT (built-in, stochastic local search, incomplete)
    dpll        Pure Python DPLL (Jeroslow-Wang heuristic, no clause learning)

Examples:
  python blackbox.py -o domain.pddl -f problem.pddl
  python blackbox.py -o domain.pddl -f problem.pddl -solver cadical
  python blackbox.py -o domain.pddl -f problem.pddl -solver -maxsec 30 glucose
  python blackbox.py -o domain.pddl -f problem.pddl -solver graphplan -then cadical
""")


if __name__ == '__main__':
    main()
