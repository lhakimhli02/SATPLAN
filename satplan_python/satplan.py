#!/usr/bin/env python3
"""
satplan.py - CLI entry point for SATplan (direct STRIPS → SAT).

Unlike BlackBox, this planner goes straight from parsed PDDL (STRIPS)
to a CNF formula without building an intermediate planning graph.

Usage:
    python satplan.py -o <domain.pddl> -f <problem.pddl> [options]
"""

from __future__ import annotations
import argparse
import sys
import time as time_mod

from data_structures import SolverSpec, Anysat, Sat, Unsat, Timeout, Failure
from data_structures import PrintLit, PrintCNF, PrintModel
from grounder import STRIPSProblem, ground_all_actions, collect_all_fluents
from satplan_planner import SATPlanner


def parse_solver_args(args: list[str]) -> list[SolverSpec]:
    """Parse the solver specification from the command line.

    Format: ``-solver {-maxsec N} <name> {-then {-maxsec N} <name> ...}``
    """
    if not args:
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
        elif tok == '-maxsec':
            i += 1
            if i < len(args):
                cur_maxsec = int(args[i])
            i += 1
        elif tok == '-maxit':
            i += 1
            if i < len(args):
                cur_maxit = int(args[i])
            i += 1
        else:
            spec = SolverSpec(
                solver_name=tok,
                solver_type=Anysat,
                maxsec=cur_maxsec,
                maxit=cur_maxit,
                argv=list(cur_argv),
            )
            specs.append(spec)
            cur_maxsec = 0
            cur_maxit = 0
            cur_argv = []
            i += 1

    if not specs:
        specs.append(SolverSpec(solver_name='cadical', solver_type=Anysat))
    return specs


def main():
    parser = argparse.ArgumentParser(
        description='SATplan - Direct STRIPS to SAT planning',
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
                        help='Force closed-world negation')
    parser.add_argument('-step', type=int, default=1,
                        help='Horizon increment step size')
    parser.add_argument('-noopt', action='store_true',
                        help='Stop at first solution (no action minimisation)')
    parser.add_argument('-noincsat', action='store_true',
                        help='Disable incremental SAT across horizons')
    parser.add_argument('-norelevance', action='store_true',
                        help='Disable action relevance pruning')
    parser.add_argument('-noeffects', action='store_true',
                        help='Disable explicit effect clauses (only frame axioms)')
    parser.add_argument('-nomutex', action='store_true',
                        help='Disable mutex constraints')
    parser.add_argument('-forallstep', action='store_true',
                        help='Use forall-step mutex semantics (default: exists-step)')
    parser.add_argument('-nocwa', action='store_true',
                        help='Disable closed-world assumption at t=0')
    parser.add_argument('-printlit', action='store_true',
                        help='Print variable map')
    parser.add_argument('-printcnf', action='store_true',
                        help='Print DIMACS CNF')
    parser.add_argument('-maxfail', type=int, default=0,
                        help='Max solver failures (0=unlimited)')
    parser.add_argument('-maxauto', type=int, default=100,
                        help='Max auto horizon (default: 100)')
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
    max_auto = args.maxauto
    max_fail = args.maxfail
    max_global_sec = args.maxglobalsec

    solver_specs = parse_solver_args(args.solver)

    global_start = time_mod.time()

    # ── 1. Load and preprocess PDDL ─────────────────────────────────────

    print("SATplan (Python) - Direct STRIPS to SAT")
    print(f"  Domain:  {domain_file}")
    print(f"  Problem: {problem_file}")
    print()

    problem = STRIPSProblem()
    problem.enable_relevance_pruning = not args.norelevance
    problem.force_neg = args.forceneg
    problem.debug = debug

    try:
        problem.load(domain_file, problem_file)
    except Exception as e:
        print(f"Error loading PDDL files: {e}", file=sys.stderr)
        sys.exit(1)

    if debug >= 1:
        print(f"  Domain: {problem.domain_name}")
        print(f"  Problem: {problem.problem_name}")
        print(f"  Action schemas: {len(problem.ops)}")
        print(f"  Objects: {len(problem.objects)}")
        print(f"  Initial facts: {len(problem.initial_facts)}")
        print(f"  Goals: {len(problem.the_goals)}")
        print()

    t_pre = time_mod.time()
    problem.process_data()
    preprocess_sec = time_mod.time() - t_pre

    if debug >= 2:
        print("=== Parsed PDDL ===")
        print(f"Action schemas ({len(problem.ops)}):")
        for op in problem.ops:
            params_str = ' '.join(op.params)
            print(f"  ({op.name} {params_str})")
            print(f"    Pre:  {op.preconds}")
            print(f"    Eff:  {op.effects}")
        print(f"\nObjects ({len(problem.objects)}): {' '.join(problem.objects)}")
        print(f"\nInitial facts ({len(problem.initial_facts)}):")
        for fact in problem.initial_facts:
            print(f"  ({' '.join(fact)})")
        print(f"\nGoals ({len(problem.the_goals)}):")
        for goal in problem.the_goals:
            if isinstance(goal, list):
                print(f"  ({' '.join(goal)})")
        print()

    # ── 2. Ground actions ────────────────────────────────────────────────

    if debug >= 1:
        print("  Grounding actions...")
    t_ground = time_mod.time()
    ground_actions = ground_all_actions(problem)
    ground_sec = time_mod.time() - t_ground

    if len(ground_actions) == 0:
        print("Error: no ground actions found", file=sys.stderr)
        sys.exit(1)

    all_fluents, initial_set, goal_literals = collect_all_fluents(
        problem, ground_actions
    )

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

    if debug >= 2:
        print("=== Ground Actions (first 20) ===")
        for ga in ground_actions[:20]:
            print(f"  {ga.name}")
            if ga.pos_pre:
                print(f"    +pre: {sorted(ga.pos_pre)}")
            if ga.neg_pre:
                print(f"    -pre: {sorted(ga.neg_pre)}")
            if ga.add_eff:
                print(f"    +eff: {sorted(ga.add_eff)}")
            if ga.del_eff:
                print(f"    -eff: {sorted(ga.del_eff)}")
        if len(ground_actions) > 20:
            print(f"  ... ({len(ground_actions) - 20} more)")
        print()

    # ── 3. Build planner ─────────────────────────────────────────────────

    printflag = 0
    if args.printlit:
        printflag |= PrintLit | PrintModel
    if args.printcnf:
        printflag |= PrintCNF | PrintModel

    planner = SATPlanner(
        ground_actions=ground_actions,
        all_fluents=all_fluents,
        initial_set=initial_set,
        goal_literals=goal_literals,
        solver_specs=solver_specs,
        printflag=printflag,
        debug=debug,
        noopt=args.noopt,
        incremental_sat=not args.noincsat,
        exists_step=not args.forallstep,
        emit_effects=not args.noeffects,
        emit_mutex=not args.nomutex,
        close_world=not args.nocwa,
    )

    max_time = fixed_time if fixed_time > 0 else max_auto

    # ── 4. Search for plan ───────────────────────────────────────────────

    if fixed_time > 0:
        if debug >= 1:
            print(f"Trying fixed horizon {fixed_time}...")
        result = planner.do_plan(fixed_time)
        if result == Sat:
            if not args.noopt:
                count = planner.minimize_plan_actions(fixed_time)
                if debug >= 1:
                    print(f"  Minimised to {count} actions")
            planner.print_plan(output_file)
        else:
            print(f"No plan found at horizon {fixed_time}")
    else:
        found = False
        fail_count = 0
        cur_time = 1

        while cur_time <= max_time:
            # Global timeout check
            if max_global_sec > 0:
                if time_mod.time() - global_start > max_global_sec:
                    print("Global time limit reached")
                    break

            if debug >= 1:
                print(f"Trying horizon {cur_time}...")

            result = planner.do_plan(cur_time)

            if result == Sat:
                # Minimise actions at current horizon
                if not args.noopt:
                    count = planner.minimize_plan_actions(cur_time)
                    best_count = count
                    best_time = cur_time
                    best_plan = planner.snapshot_plan()

                    if debug >= 1:
                        print(f"  Horizon {cur_time}: {best_count} actions")

                    # Search longer horizons (a more serial plan may use fewer actions)
                    stall = 0
                    for extra in range(1, best_count + 1):
                        ext_time = cur_time + extra
                        if ext_time > max_time:
                            break
                        if max_global_sec > 0:
                            if time_mod.time() - global_start > max_global_sec:
                                break
                        ext_count = planner.minimize_plan_actions(ext_time)
                        if ext_count < 0:
                            stall += 1
                            if stall >= 3:
                                break
                            continue
                        if debug >= 1:
                            print(f"  Horizon {ext_time}: {ext_count} actions")
                        if ext_count < best_count:
                            best_count = ext_count
                            best_time = ext_time
                            best_plan = planner.snapshot_plan()
                            stall = 0
                        else:
                            stall += 1
                            if stall >= 3:
                                break

                    planner.restore_plan(best_plan)
                    planner.plan_time = best_time

                planner.print_plan(output_file)
                found = True
                break

            elif result == Unsat:
                if debug >= 1:
                    print(f"  No plan at horizon {cur_time}")
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
                print(f"No plan found up to horizon {max_time}")

    # ── 5. Print timing ──────────────────────────────────────────────────

    elapsed = time_mod.time() - global_start
    print()
    if elapsed < 60:
        print(f"Total time: {elapsed:.2f} seconds")
    else:
        print(f"Total time: {elapsed / 60:.2f} minutes ({elapsed:.1f} seconds)")

    timing = planner.get_timing_stats()
    print("Timing breakdown:")
    print(f"  Preprocessing:  {preprocess_sec:.3f}s")
    print(f"  Grounding:      {ground_sec:.3f}s")
    print(f"  CNF generation: {timing['sat_encode_sec']:.3f}s")
    print(f"  SAT solve:      {timing['sat_solve_sec']:.3f}s ({timing['sat_calls']} calls)")


def _print_usage():
    print("""
SATplan (Python) - Direct STRIPS to SAT

Unlike BlackBox, this planner encodes STRIPS actions directly as CNF
without an intermediate planning graph.

Usage:
  python satplan.py -o <domain.pddl> -f <problem.pddl> [options]

Required:
  -o <file>         Domain PDDL file
  -f <file>         Problem PDDL file

Options:
  -g <file>         Output plan file
  -t <int>          Fixed horizon (0 = auto)
  -i <level>        Debug level (0-2)
  -n                Force closed-world negation
  -step <n>         Horizon increment step size (default: 1)
  -noopt            Stop at first solution (no action minimisation)
  -noincsat         Disable incremental SAT across horizons
  -norelevance      Disable action relevance pruning
  -noeffects        Omit explicit effect clauses (rely on frame axioms only)
  -nomutex          Disable mutex (action interference) constraints
  -forallstep       Use forall-step mutex semantics (default: exists-step)
  -nocwa            Disable closed-world assumption at t=0
  -printlit         Print variable map
  -printcnf         Print DIMACS CNF
  -maxfail <n>      Max solver failures (0=unlimited)
  -maxauto <n>      Max auto horizon (default: 100)
  -maxglobalsec <n> Global time limit in seconds

Solver specification:
  -solver {-maxsec N} <solver> {-then {-maxsec N} <solver> ...}

  Available solvers:
    cadical   CaDiCaL 1.9.5 (default, via PySAT)
    glucose   Glucose 4.2 (via PySAT)
    maple     MapleChrono (via PySAT)
    minisat   MiniSat (via PySAT)
    kissat    Kissat (external binary)
    walksat   WalkSAT (stochastic local search, incomplete)
    dpll      Pure Python DPLL

Examples:
  python satplan.py -o domain.pddl -f problem.pddl
  python satplan.py -o domain.pddl -f problem.pddl -solver cadical
  python satplan.py -o domain.pddl -f problem.pddl -t 6 -i 1
  python satplan.py -o domain.pddl -f problem.pddl -noopt -noincsat
  python satplan.py -o domain.pddl -f problem.pddl -forallstep -nomutex
""")


if __name__ == '__main__':
    main()
