"""
planner.py - Search orchestration & backward-chaining solver.

Replaces: planner.cpp

Contains the main planning loop (``do_plan``), backward search
(``basicplan``), solver chaining, and plan output.
"""

from __future__ import annotations
import sys
import time as time_mod
from typing import Optional

from data_structures import (
    Vertex, HashTable, SolverSpec,
    Sat, Unsat, Timeout, Failure,
    Graphplan_Solver, Anysat,
    CONNECTOR, NOOP,
    PrintLit, PrintCNF, PrintModel,
)
from graphplan import PlanningGraph
from graph2wff import SATEncoder
from sat_interface import (
    bb_satsolve_cadical, bb_satsolve_glucose, bb_satsolve_maple,
    bb_satsolve_minisat, bb_satsolve_kissat, bb_satsolve_walksat, bb_satsolve_dpll,
    IncrementalSATSolver,
)
from justify import justify_plan
from utilities import are_mutex, SetTable, can_hope_to_solve


# ── Planner ──────────────────────────────────────────────────────────────────

class Planner:
    """Main planning orchestrator."""

    def __init__(self, graph: PlanningGraph, solver_specs: list[SolverSpec],
                 axioms: int = 7, printflag: int = 0, debug: int = 0,
                 do_justify: bool = True, noopt: bool = False,
                 noskip: bool = False, incremental_sat: bool = True):
        self.graph = graph
        self.solver_specs = solver_specs
        self.axioms = axioms
        self.printflag = printflag
        self.debug = debug
        self.do_justify = do_justify
        self.noopt = noopt        # stop at first solution (don't optimise)
        self.noskip = noskip      # don't skip graphplan even when SAT present
        self.incremental_sat = incremental_sat

        # Backward search state
        self.bad_table = SetTable()
        self.good_table = SetTable()
        self.do_subsets: bool = True
        self.do_lower: bool = False
        self.num_acts_tried: int = 0

        # Iteration / time limits
        self.current_it: int = 0
        self.max_it: int = 0
        self.max_sec: int = 0
        self.start_time: float = 0.0

        # Result
        self.plan_found: bool = False
        self.plan_time: int = 0
        # If GraphPlan timed out and -noskip is not set, skip GraphPlan
        # on later horizons and rely on SAT-based solvers.
        self._skip_graphplan: bool = False
        # SAT timing totals (seconds)
        self._sat_encode_total_sec: float = 0.0
        self._sat_solve_total_sec: float = 0.0
        self._sat_calls: int = 0
        # Per solver-spec incremental SAT state across horizons.
        self._inc_sat_states: dict[int, dict] = {}

    # ── Main planning loop ───────────────────────────────────────────────

    def do_plan(self, maxtime: int) -> int:
        """Run solvers at plan length *maxtime*.

        Returns one of ``Sat``, ``Unsat``, ``Timeout``, ``Failure``.
        """
        # Setup goals at this time step
        num_goals = self.graph.setup_goals(maxtime)
        if num_goals == 0:
            return Unsat

        # Iterate through solver specs
        saw_timeout = False
        saw_failure = False
        found_sat = False
        best_action_count: int | None = None
        best_plan_snapshot: list[int] | None = None

        sat_bundle: tuple[SATEncoder, list[list[int]], int, int] | None = None

        for spec_idx, spec in enumerate(list(self.solver_specs)):
            if spec.solver_name == 'graphplan' and self._skip_graphplan:
                if self.debug >= 1:
                    print("  Skipping graphplan after previous timeout")
                continue
            self.max_sec = spec.maxsec
            self.max_it = spec.maxit

            if spec.solver_name == 'graphplan':
                result = self._run_graphplan(maxtime, num_goals)
            else:
                if self.incremental_sat:
                    result = self._run_sat_solver_incremental(
                        maxtime, num_goals, spec_idx, spec
                    )
                else:
                    result, sat_bundle = self._run_sat_solver(
                        maxtime, num_goals, spec, sat_bundle
                    )

            if result == Sat:
                # Preserve this candidate; optionally continue trying
                # other solvers when optimisation is enabled.
                action_count = self._count_plan_actions(maxtime)
                if best_action_count is None or action_count < best_action_count:
                    best_action_count = action_count
                    best_plan_snapshot = self._snapshot_plan_usage(maxtime)
                found_sat = True
                if self.noopt:
                    if self.do_justify:
                        justify_plan(self.graph, maxtime)
                    self.plan_found = True
                    self.plan_time = maxtime
                    return Sat
                continue
            elif result == Unsat:
                # Unsat is conclusive only if no solver has already found SAT.
                if not found_sat:
                    return Unsat
                continue
            elif result == Timeout:
                saw_timeout = True
                if spec.solver_name == 'graphplan' and not self.noskip:
                    self._skip_graphplan = True
                if self.debug >= 1:
                    print(f"  Solver {spec.solver_name} timed out at time {maxtime}")
                continue  # try next solver
            else:
                saw_failure = True
                if self.debug >= 1:
                    print(f"  Solver {spec.solver_name} failed at time {maxtime}")
                continue

        if found_sat:
            if best_plan_snapshot is not None:
                self._restore_plan_usage(maxtime, best_plan_snapshot)
            if self.do_justify:
                justify_plan(self.graph, maxtime)
            self.plan_found = True
            self.plan_time = maxtime
            return Sat
        if saw_timeout:
            return Timeout
        if saw_failure:
            return Failure
        return Failure

    def _run_graphplan(self, maxtime: int, num_goals: int) -> int:
        """Run GraphPlan backward-chaining search."""
        if self.debug >= 1:
            print(f"  Running GraphPlan at time {maxtime}...")

        self.start_time = time_mod.time()
        self.current_it = 0
        # Reset per-search mutable flags (mirrors C behavior where recursion
        # leaves these balanced except chosen operators for printing).
        for t in range(maxtime):
            self.graph.goals_at[t] = []
        for t in range(maxtime + 1):
            for fv in self.graph.fact_table[t]:
                fv.used = 0
                if t > 0:
                    fv.is_true = 0
        for t in range(maxtime):
            for op in self.graph.op_table[t]:
                op.used = 0
                op.cant_do = 0

        goal_count = len(self.graph.goals_at[maxtime])

        # Lower-bound check
        if self.do_lower:
            if not can_hope_to_solve(self.graph.goals_at[maxtime], maxtime):
                if self.debug >= 1:
                    print("  Lower bound prune: cannot solve at this time step")
                return Unsat

        # Run backward search
        self.num_acts_tried = 0
        for g in self.graph.goals_at[maxtime]:
            g.used += 1
        try:
            result = self._basicplan(goal_count - 1, 0, maxtime)
        finally:
            for g in self.graph.goals_at[maxtime]:
                g.used = max(0, g.used - 1)

        if result == 1:
            return Sat
        elif result == 0:
            return Unsat
        else:
            return Timeout

    def _run_sat_solver(
        self,
        maxtime: int,
        num_goals: int,
        spec: SolverSpec,
        sat_bundle: tuple[SATEncoder, list[list[int]], int, int] | None = None,
    ) -> tuple[int, tuple[SATEncoder, list[list[int]], int, int] | None]:
        """Encode to SAT and call an external solver."""
        if self.debug >= 1:
            print(f"  Running {spec.solver_name} at time {maxtime}...")

        encode_sec = 0.0
        if sat_bundle is None:
            encoder = SATEncoder(self.graph, self.axioms, self.printflag)
            t0 = time_mod.time()
            clauses, numvar, numclause = encoder.encode(maxtime, num_goals)
            encode_sec = time_mod.time() - t0
            self._sat_encode_total_sec += encode_sec
            sat_bundle = (encoder, clauses, numvar, numclause)
        else:
            encoder, clauses, numvar, numclause = sat_bundle

        if self.debug >= 1:
            print(f"  CNF: {numvar} vars, {numclause} clauses")

        if self.printflag & PrintLit:
            print("\n=== Variable Map ===")
            encoder.print_variable_map()
        if self.printflag & PrintCNF:
            print("\n=== DIMACS CNF ===")
            print(encoder.to_dimacs())

        # Call the appropriate solver
        solver_func = {
            'cadical': bb_satsolve_cadical,
            'cd195': bb_satsolve_cadical,
            'glucose': bb_satsolve_glucose,
            'g42': bb_satsolve_glucose,
            'maple': bb_satsolve_maple,
            'mcb': bb_satsolve_maple,
            'minisat': bb_satsolve_minisat,
            'mgh': bb_satsolve_minisat,
            'kissat': bb_satsolve_kissat,
            'walksat': bb_satsolve_walksat,
            'dpll': bb_satsolve_dpll,
        }.get(spec.solver_name)

        if solver_func is None:
            print(f"  Unknown solver: {spec.solver_name}", file=sys.stderr)
            return Failure, sat_bundle

        t1 = time_mod.time()
        status, soln = solver_func(clauses, numvar, numclause,
                                   maxtime=spec.maxsec,
                                   extra_args=spec.argv,
                                   debug=self.debug)
        solve_sec = time_mod.time() - t1
        self._sat_solve_total_sec += solve_sec
        self._sat_calls += 1

        if self.debug >= 1:
            print(f"  SAT timing: encode={encode_sec:.3f}s solve={solve_sec:.3f}s")

        if status == Sat:
            if self.printflag & PrintModel:
                print(f"\n=== SAT Solution (makespan {maxtime}) ===")
                for i in range(1, numvar + 1):
                    if i < len(soln) and soln[i] == 1:
                        v = encoder.prop2vertex[i] if i < len(encoder.prop2vertex) else None
                        name = v.name if v is not None else f"aux_{i}"
                        print(f"  {i}: {name} = TRUE")
            encoder.soln2graph(soln)
            return Sat, sat_bundle
        return status, sat_bundle

    def _run_sat_solver_incremental(self, maxtime: int, num_goals: int,
                                    spec_idx: int, spec: SolverSpec) -> int:
        """Incremental SAT across horizons using assumptions for goals."""
        if self.debug >= 1:
            print(f"  Running {spec.solver_name} incrementally at time {maxtime}...")

        # Non-incremental solvers fall back to one-shot solving.
        if spec.solver_name in ('kissat', 'walksat', 'dpll'):
            if self.debug >= 1:
                print(f"  {spec.solver_name} does not support incremental mode, "
                      "falling back to non-incremental")
            result, _ = self._run_sat_solver(maxtime, num_goals, spec)
            return result

        # Unknown solver names cannot be handled.
        if spec.solver_name not in (
            'cadical', 'cd195', 'glucose', 'g42', 'maple', 'mcb',
            'minisat', 'mgh',
        ):
            print(f"  Unknown solver: {spec.solver_name}", file=sys.stderr)
            return Failure

        state = self._inc_sat_states.get(spec_idx)
        if state is None or state.get('solver_name') != spec.solver_name:
            try:
                state = {
                    'solver_name': spec.solver_name,
                    'encoder': SATEncoder(self.graph, self.axioms, self.printflag),
                    'session': IncrementalSATSolver(spec.solver_name, debug=self.debug),
                    'numclause': 0,
                    'numvar': 0,
                }
            except Exception as e:
                print(f"  SAT solver error: {e}", file=sys.stderr)
                return Failure
            self._inc_sat_states[spec_idx] = state

        encoder: SATEncoder = state['encoder']
        session: IncrementalSATSolver = state['session']

        t0 = time_mod.time()
        clauses, numvar, numclause = encoder.encode(
            maxtime, num_goals, incremental=True
        )
        encode_sec = time_mod.time() - t0
        self._sat_encode_total_sec += encode_sec

        # The encoder now only returns clauses for newly-encoded layers,
        # so all returned clauses are the delta to add.
        total_clauses = state['numclause'] + numclause

        if self.debug >= 1:
            print(f"  CNF: {numvar} vars, {total_clauses} clauses")

        if self.printflag & PrintLit:
            print("\n=== Variable Map ===")
            encoder.print_variable_map()
        if self.printflag & PrintCNF:
            print(f"\n=== DIMACS CNF (delta, {len(clauses)} new clauses) ===")
            for clause in clauses:
                print(' '.join(str(lit) for lit in clause) + ' 0')

        if clauses:
            session.add_clauses(clauses)
            if self.debug >= 1:
                print(f"  Added {len(clauses)} new clauses incrementally")

        state['numclause'] = total_clauses
        state['numvar'] = numvar

        goal_assumptions = encoder.get_goal_assumptions()

        t1 = time_mod.time()
        status, soln = session.solve(
            numvar=numvar,
            maxtime=spec.maxsec,
            assumptions=goal_assumptions,
        )
        solve_sec = time_mod.time() - t1
        self._sat_solve_total_sec += solve_sec
        self._sat_calls += 1

        if self.debug >= 1:
            print(
                f"  SAT timing: encode={encode_sec:.3f}s solve={solve_sec:.3f}s"
            )

        if status == Sat:
            if self.printflag & PrintModel:
                print(f"\n=== SAT Solution (makespan {maxtime}) ===")
                for i in range(1, numvar + 1):
                    if i < len(soln) and soln[i] == 1:
                        v = encoder.prop2vertex[i] if i < len(encoder.prop2vertex) else None
                        name = v.name if v is not None else f"aux_{i}"
                        print(f"  {i}: {name} = TRUE")
            encoder.soln2graph(soln)
        return status

    def minimize_plan_actions(self, maxtime: int, num_goals: int) -> int:
        """Re-encode at *maxtime* with a fresh solver and minimize actions.

        Uses cardinality constraints (PySAT sequential counter) to iteratively
        tighten the action bound until UNSAT, returning the minimum action
        count.  Updates graph vertex ``used`` flags with the best solution.
        """
        from pysat.card import CardEnc, EncType

        encoder = SATEncoder(self.graph, self.axioms, self.printflag)
        clauses, numvar, numclause = encoder.encode(maxtime, num_goals)

        # Collect non-NOOP action variables (only those assigned by this encoder).
        action_vars: list[int] = []
        for t in range(maxtime):
            for op in self.graph.op_table[t]:
                if op.needed and op.prop != 0 and op.prop <= numvar and not op.is_noop:
                    action_vars.append(op.prop)

        if not action_vars:
            return 0

        # Fresh solver with the base clauses.
        opt_session = IncrementalSATSolver(
            solver_name='cadical', debug=0,
        )
        opt_session.add_clauses(clauses)

        # Initial solve to get a starting point.
        goal_lits = [gv.prop for gv in self.graph.goals_at[maxtime] if gv.prop != 0]
        status, soln = opt_session.solve(numvar=numvar, assumptions=goal_lits)
        if status != Sat:
            opt_session.delete()
            return -1

        current_count = sum(1 for v in action_vars if v < len(soln) and soln[v] == 1)
        best_soln = soln
        top_var = numvar

        # Iteratively tighten.
        while current_count > 0:
            bound = current_count - 1
            card_clauses = CardEnc.atmost(
                lits=action_vars, bound=bound,
                top_id=top_var, encoding=EncType.seqcounter,
            )
            if not card_clauses.clauses:
                break
            new_top = max(abs(lit) for cl in card_clauses.clauses for lit in cl)
            top_var = max(top_var, new_top)

            opt_session.add_clauses(card_clauses.clauses)
            status, new_soln = opt_session.solve(
                numvar=top_var, assumptions=goal_lits,
            )
            self._sat_calls += 1

            if status != Sat:
                break

            best_soln = new_soln
            new_count = sum(
                1 for v in action_vars if v < len(new_soln) and new_soln[v] == 1
            )
            if self.debug >= 1:
                print(f"  Action minimization: {current_count} -> {new_count}")
            current_count = new_count

        opt_session.delete()

        # Map best solution back to graph.
        encoder.soln2graph(best_soln)
        return current_count

    def get_timing_stats(self) -> dict[str, float | int]:
        """Return cumulative SAT timing counters."""
        return {
            'sat_encode_sec': self._sat_encode_total_sec,
            'sat_solve_sec': self._sat_solve_total_sec,
            'sat_calls': self._sat_calls,
        }

    # ── Backward search (basicplan) ──────────────────────────────────────

    def _basicplan(self, cindex: int, nindex: int, time: int) -> int:
        """Recursive backward-chaining search.

        Parameters
        ----------
        cindex : int
            Current goal index (counting down to -1).
        nindex : int
            Next-layer goal index (counting up).
        time : int
            Current time step.

        Returns 1=found, 0=not found, 2=timeout.
        """
        if time <= 0:
            return 1  # success: reached initial state

        # Check time limit
        if self.max_sec > 0:
            elapsed = time_mod.time() - self.start_time
            if elapsed > self.max_sec:
                return Timeout

        # Check iteration limit
        if self.max_it > 0:
            self.current_it += 1
            if self.current_it > self.max_it:
                return Timeout

        goals = self.graph.goals_at[time]

        # All goals at this level processed → recurse to previous level
        if cindex < 0:
            if time - 1 < 0:
                return 1
            check_goals = self.graph.goals_at[time - 1][:nindex] if nindex > 0 else []

            if nindex > 0:
                if self.bad_table.lookup(check_goals, time - 1):
                    return 0
                if self.do_subsets and self.bad_table.subset_lookup(check_goals, time - 1):
                    return 0
                if not self._action_set_is_minimal(nindex, time - 1):
                    return 0
                if self.do_lower and not can_hope_to_solve(check_goals, time - 1):
                    self.bad_table.insert(check_goals, time - 1)
                    return 0

            # Recurse to previous time step
            result = self._basicplan(nindex - 1, 0, time - 1)

            if result == 0:
                # Memoise failure
                if nindex > 0:
                    self.bad_table.insert(
                        self.graph.goals_at[time - 1][:nindex], time - 1)
            return result

        # Skip goals already achieved by currently selected operators
        while cindex >= 0 and goals[cindex].is_true:
            cindex -= 1
        if cindex < 0:
            return self._basicplan(-1, nindex, time)
        v = goals[cindex]

        # Try each producer (NOOPs first since they're at front of in_edges)
        for op in v.in_edges:
            # Skip if operator is marked exclusive with current choices
            if op.cant_do > 0:
                continue

            # Select this operator
            self._mark_exclusive(op)
            # Check if remaining goals still possible under this commitment
            if not self._goals_still_possible(cindex, time):
                self._unmark_exclusive(op)
                continue

            op.used += 1
            if not op.is_noop:
                self.num_acts_tried += 1

            # Add preconditions
            new_nindex = self._add_preconditions(op, time, nindex)
            for eff in op.out_edges:
                eff.is_true += 1

            result = self._basicplan(cindex - 1, new_nindex, time)

            # Undo transient search state (keep op.used on successful path)
            for eff in op.out_edges:
                eff.is_true -= 1
            new_nindex = self._remove_preconditions(op, time, new_nindex)
            self._unmark_exclusive(op)

            if result == 1:
                return 1
            if result == Timeout:
                op.used = max(0, op.used - 1)
                return Timeout

            # Backtrack
            op.used = max(0, op.used - 1)

        return 0  # no producer worked

    def _mark_exclusive(self, op: Vertex):
        """Mark all operators exclusive with *op* as cant_do."""
        for excl in op.exclusive:
            excl.cant_do += 1

    def _unmark_exclusive(self, op: Vertex):
        """Unmark exclusive operators."""
        for excl in op.exclusive:
            excl.cant_do -= 1

    def _goals_still_possible(self, index: int, time: int) -> bool:
        """Check if remaining goals [0,index) still have an unmarked producer."""
        goals = self.graph.goals_at[time]
        for i in range(index):
            v = goals[i]
            if v.is_true:
                continue
            # Check that at least one producer is not cant_do
            has_producer = False
            for op in v.in_edges:
                if op.cant_do <= 0:
                    has_producer = True
                    break
            if not has_producer:
                return False
        return True

    def _add_preconditions(self, op: Vertex, time: int, nindex: int) -> int:
        """Add op preconditions as goals at time-1 and return new nindex."""
        if time - 1 >= len(self.graph.goals_at):
            return nindex
        prev_goals = self.graph.goals_at[time - 1]
        for prec in op.in_edges:
            was_used = prec.used
            prec.used += 1
            if was_used == 0:
                prev_goals.append(prec)
                nindex += 1
        return nindex

    def _remove_preconditions(self, op: Vertex, time: int, nindex: int) -> int:
        """Undo _add_preconditions for *op* and return updated nindex."""
        if time - 1 >= len(self.graph.goals_at):
            return nindex
        prev_goals = self.graph.goals_at[time - 1]
        for prec in op.in_edges:
            prec.used -= 1
            if prec.used == 0 and nindex > 0:
                nindex -= 1
                if prev_goals:
                    prev_goals.pop()
        return nindex

    def _action_set_is_minimal(self, index: int, time: int) -> bool:
        """Check if any selected operator can be removed while preserving goals."""
        if time < 0 or index <= 0:
            return True
        goals = self.graph.goals_at[time]
        for i in range(index):
            goal = goals[i]
            for op in goal.out_edges:
                if not op.used:
                    continue
                needed = False
                for eff in op.out_edges:
                    if eff.used and eff.is_true == 1:
                        needed = True
                        break
                if not needed:
                    return False
        return True

    def _snapshot_plan_usage(self, maxtime: int) -> list[int]:
        """Capture used flags for operator layers up to *maxtime*."""
        snapshot: list[int] = []
        for t in range(maxtime):
            for op in self.graph.op_table[t]:
                snapshot.append(op.used)
        return snapshot

    def _restore_plan_usage(self, maxtime: int, snapshot: list[int]):
        """Restore used flags from a snapshot created by _snapshot_plan_usage."""
        idx = 0
        for t in range(maxtime):
            for op in self.graph.op_table[t]:
                if idx < len(snapshot):
                    op.used = snapshot[idx]
                else:
                    op.used = 0
                idx += 1

    def _count_plan_actions(self, maxtime: int) -> int:
        """Count selected non-NOOP actions in the current plan."""
        count = 0
        for t in range(maxtime):
            for op in self.graph.op_table[t]:
                if op.used and not op.is_noop:
                    count += 1
        return count

    # ── Plan output ──────────────────────────────────────────────────────

    def print_plan(self, maxtime: int, output_file: Optional[str] = None):
        """Print the extracted plan."""
        lines: list[str] = []
        action_count = 0

        lines.append("")
        lines.append("Begin plan")

        for t in range(maxtime):
            step_actions: list[str] = []
            for op in self.graph.op_table[t]:
                if op.used and not op.is_noop:
                    step_actions.append(op.name)
                    action_count += 1
            for act_name in sorted(step_actions):
                lines.append(f"{t + 1}: {_pretty_action(act_name)}")

        lines.append("End plan")
        lines.append(f"{action_count} actions in plan")
        lines.append("")

        output = '\n'.join(lines)
        print(output)

        if output_file:
            with open(output_file, 'w') as f:
                f.write(output + '\n')

    def print_stats(self):
        """Print search statistics."""
        print(f"  Actions tried: {self.num_acts_tried}")
        print(f"  Bad table: {self.bad_table.inserts} inserts, "
              f"{self.bad_table.hits} hits")


def _pretty_action(name: str) -> str:
    """Convert ``move_a_b_c`` to ``(move a b c)``."""
    parts = name.split(CONNECTOR)
    return '(' + ' '.join(parts) + ')'
