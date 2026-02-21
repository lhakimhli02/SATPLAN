"""
satplan_planner.py - Planning search orchestration for direct STRIPS-to-SAT.

Manages the horizon-iterating planning loop, calling the STRIPSEncoder and
SAT solvers. Supports incremental SAT, action minimisation, and plan output.
"""

from __future__ import annotations
import sys
import time as time_mod
from typing import Optional

from data_structures import Sat, Unsat, Timeout, Failure, SolverSpec, CONNECTOR
from strips_encoder import STRIPSEncoder, PrintLit, PrintCNF, PrintModel
from grounder import GroundAction
from sat_interface import (
    bb_satsolve_cadical, bb_satsolve_glucose, bb_satsolve_maple,
    bb_satsolve_minisat, bb_satsolve_kissat, bb_satsolve_walksat, bb_satsolve_dpll,
    IncrementalSATSolver,
)


_SOLVER_FUNCS = {
    'cadical': bb_satsolve_cadical,
    'cd195':   bb_satsolve_cadical,
    'glucose': bb_satsolve_glucose,
    'g42':     bb_satsolve_glucose,
    'maple':   bb_satsolve_maple,
    'mcb':     bb_satsolve_maple,
    'minisat': bb_satsolve_minisat,
    'mgh':     bb_satsolve_minisat,
    'kissat':  bb_satsolve_kissat,
    'walksat': bb_satsolve_walksat,
    'dpll':    bb_satsolve_dpll,
}

_INCREMENTAL_SOLVERS = frozenset({
    'cadical', 'cd195', 'glucose', 'g42', 'maple', 'mcb', 'minisat', 'mgh',
})


class SATPlanner:
    """Orchestrates the STRIPS → SAT planning search."""

    def __init__(self,
                 ground_actions: list[GroundAction],
                 all_fluents: list[str],
                 initial_set: set[str],
                 goal_literals: list[tuple[bool, str]],
                 solver_specs: list[SolverSpec],
                 printflag: int = 0,
                 debug: int = 0,
                 noopt: bool = False,
                 incremental_sat: bool = True,
                 exists_step: bool = True,
                 emit_effects: bool = True,
                 emit_mutex: bool = True,
                 close_world: bool = True):
        self.ground_actions = ground_actions
        self.all_fluents = all_fluents
        self.initial_set = initial_set
        self.goal_literals = goal_literals
        self.solver_specs = solver_specs
        self.printflag = printflag
        self.debug = debug
        self.noopt = noopt
        self.incremental_sat = incremental_sat
        self.exists_step = exists_step
        self.emit_effects = emit_effects
        self.emit_mutex = emit_mutex
        self.close_world = close_world

        # Plan state
        self.plan_found: bool = False
        self.plan_time: int = 0
        self._plan: list[list[str]] = []  # per-step action names

        # Timing
        self._sat_encode_sec: float = 0.0
        self._sat_solve_sec: float = 0.0
        self._sat_calls: int = 0

        # Incremental session state per solver spec index
        self._inc_states: dict[int, dict] = {}

    def _make_encoder(self) -> STRIPSEncoder:
        return STRIPSEncoder(
            ground_actions=self.ground_actions,
            all_fluents=self.all_fluents,
            initial_set=self.initial_set,
            goal_literals=self.goal_literals,
            printflag=self.printflag,
            exists_step=self.exists_step,
            emit_effects=self.emit_effects,
            emit_mutex=self.emit_mutex,
            close_world=self.close_world,
        )

    # ── Main search call ──────────────────────────────────────────────────

    def do_plan(self, maxtime: int) -> int:
        """Try to find a plan of length *maxtime*. Returns Sat/Unsat/Timeout/Failure."""
        saw_timeout = False
        saw_failure = False
        found_sat = False
        best_count: Optional[int] = None
        best_plan: Optional[list[list[str]]] = None

        for spec_idx, spec in enumerate(self.solver_specs):
            if self.incremental_sat and spec.solver_name in _INCREMENTAL_SOLVERS:
                result = self._run_incremental(maxtime, spec_idx, spec)
            else:
                result = self._run_oneshot(maxtime, spec)

            if result == Sat:
                if best_count is None:
                    best_count = self._count_plan_actions()
                    best_plan = [list(step) for step in self._plan]
                found_sat = True
                if self.noopt:
                    self.plan_found = True
                    self.plan_time = maxtime
                    return Sat
            elif result == Unsat:
                if not found_sat:
                    return Unsat
            elif result == Timeout:
                saw_timeout = True
            else:
                saw_failure = True

        if found_sat:
            if best_plan is not None:
                self._plan = best_plan
            self.plan_found = True
            self.plan_time = maxtime
            return Sat
        if saw_timeout:
            return Timeout
        return Failure

    # ── One-shot solver ───────────────────────────────────────────────────

    def _run_oneshot(self, maxtime: int, spec: SolverSpec) -> int:
        if self.debug >= 1:
            print(f"  Running {spec.solver_name} at horizon {maxtime}...")

        encoder = self._make_encoder()
        t0 = time_mod.time()
        clauses, numvar, numclause = encoder.encode(maxtime, incremental=False)
        encode_sec = time_mod.time() - t0
        self._sat_encode_sec += encode_sec

        if self.debug >= 1:
            print(f"  CNF: {numvar} vars, {numclause} clauses")

        self._print_debug(encoder, clauses, maxtime)

        solver_func = _SOLVER_FUNCS.get(spec.solver_name)
        if solver_func is None:
            print(f"  Unknown solver: {spec.solver_name}", file=sys.stderr)
            return Failure

        t1 = time_mod.time()
        status, soln = solver_func(clauses, numvar, numclause,
                                   maxtime=spec.maxsec,
                                   extra_args=spec.argv,
                                   debug=self.debug)
        solve_sec = time_mod.time() - t1
        self._sat_solve_sec += solve_sec
        self._sat_calls += 1

        if self.debug >= 1:
            print(f"  SAT: encode={encode_sec:.3f}s solve={solve_sec:.3f}s")

        if status == Sat:
            self._print_model(soln, numvar, encoder, maxtime)
            self._plan = encoder.extract_plan(soln, maxtime)
        return status

    # ── Incremental solver ────────────────────────────────────────────────

    def _run_incremental(self, maxtime: int, spec_idx: int,
                         spec: SolverSpec) -> int:
        if self.debug >= 1:
            print(f"  Running {spec.solver_name} incrementally at horizon {maxtime}...")

        state = self._inc_states.get(spec_idx)
        if state is None or state.get('solver_name') != spec.solver_name:
            try:
                state = {
                    'solver_name': spec.solver_name,
                    'encoder': self._make_encoder(),
                    'session': IncrementalSATSolver(spec.solver_name, debug=self.debug),
                    'total_clauses': 0,
                    'numvar': 0,
                }
            except Exception as e:
                print(f"  SAT solver error: {e}", file=sys.stderr)
                return Failure
            self._inc_states[spec_idx] = state

        encoder: STRIPSEncoder = state['encoder']
        session: IncrementalSATSolver = state['session']

        t0 = time_mod.time()
        clauses, numvar, numclause = encoder.encode(maxtime, incremental=True)
        encode_sec = time_mod.time() - t0
        self._sat_encode_sec += encode_sec

        total_clauses = state['total_clauses'] + numclause
        state['total_clauses'] = total_clauses
        state['numvar'] = numvar

        if self.debug >= 1:
            print(f"  CNF: {numvar} vars, {total_clauses} clauses "
                  f"(+{numclause} new)")

        if self.printflag & PrintLit:
            print("\n=== Variable Map ===")
            encoder.print_variable_map()
        if self.printflag & PrintCNF:
            print(f"\n=== DIMACS CNF (delta, {len(clauses)} new clauses) ===")
            for clause in clauses:
                print(' '.join(str(lit) for lit in clause) + ' 0')

        if clauses:
            session.add_clauses(clauses)

        goal_assumptions = encoder.get_goal_assumptions()

        t1 = time_mod.time()
        status, soln = session.solve(
            numvar=numvar,
            maxtime=spec.maxsec,
            assumptions=goal_assumptions,
        )
        solve_sec = time_mod.time() - t1
        self._sat_solve_sec += solve_sec
        self._sat_calls += 1

        if self.debug >= 1:
            print(f"  SAT: encode={encode_sec:.3f}s solve={solve_sec:.3f}s")

        if status == Sat:
            self._print_model(soln, numvar, encoder, maxtime)
            self._plan = encoder.extract_plan(soln, maxtime)
        return status

    # ── Action minimisation ───────────────────────────────────────────────

    def minimize_plan_actions(self, maxtime: int) -> int:
        """Minimise the number of actions in the plan at *maxtime*.

        Returns the minimum action count, or -1 if unsatisfiable.
        Updates self._plan with the minimised plan.
        """
        from pysat.card import CardEnc, EncType

        encoder = self._make_encoder()
        clauses, numvar, _ = encoder.encode(maxtime, incremental=False)

        # Collect all action variables at all time steps
        action_vars: list[int] = []
        for t in range(maxtime):
            action_vars.extend(encoder.get_action_vars_at(t))

        if not action_vars:
            return 0

        opt_session = IncrementalSATSolver('cadical', debug=0)
        opt_session.add_clauses(clauses)

        goal_lits = encoder.get_goal_assumptions()
        # For non-incremental encoding, goals are in clauses already;
        # use empty assumptions (goals are hard constraints).
        status, soln = opt_session.solve(numvar=numvar, assumptions=[])
        if status != Sat:
            opt_session.delete()
            return -1

        current_count = sum(1 for v in action_vars if v < len(soln) and soln[v] == 1)
        best_soln = soln
        top_var = numvar

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
            status, new_soln = opt_session.solve(numvar=top_var, assumptions=[])
            self._sat_calls += 1

            if status != Sat:
                break

            best_soln = new_soln
            new_count = sum(
                1 for v in action_vars
                if v < len(new_soln) and new_soln[v] == 1
            )
            if self.debug >= 1:
                print(f"  Action minimisation: {current_count} -> {new_count}")
            current_count = new_count

        opt_session.delete()
        self._plan = encoder.extract_plan(best_soln, maxtime)
        return current_count

    # ── Plan state helpers ────────────────────────────────────────────────

    def _count_plan_actions(self) -> int:
        return sum(len(step) for step in self._plan)

    def snapshot_plan(self) -> list[list[str]]:
        return [list(step) for step in self._plan]

    def restore_plan(self, snapshot: list[list[str]]):
        self._plan = snapshot

    # ── Output ───────────────────────────────────────────────────────────

    def print_plan(self, output_file: Optional[str] = None):
        """Print the found plan."""
        lines: list[str] = []
        lines.append("")
        lines.append("Begin plan")

        action_count = 0
        for t, step_actions in enumerate(self._plan):
            for act_name in sorted(step_actions):
                lines.append(f"{t + 1}: {_pretty_action(act_name)}")
                action_count += 1

        lines.append("End plan")
        lines.append(f"{action_count} actions in plan")
        lines.append("")

        output = '\n'.join(lines)
        print(output)

        if output_file:
            with open(output_file, 'w') as fh:
                fh.write(output + '\n')

    def get_timing_stats(self) -> dict:
        return {
            'sat_encode_sec': self._sat_encode_sec,
            'sat_solve_sec': self._sat_solve_sec,
            'sat_calls': self._sat_calls,
        }

    # ── Debug helpers ─────────────────────────────────────────────────────

    def _print_debug(self, encoder: STRIPSEncoder, clauses: list, maxtime: int):
        if self.printflag & PrintLit:
            print("\n=== Variable Map ===")
            encoder.print_variable_map()
        if self.printflag & PrintCNF:
            print("\n=== DIMACS CNF ===")
            print(encoder.to_dimacs())

    def _print_model(self, soln: list[int], numvar: int,
                     encoder: STRIPSEncoder, maxtime: int):
        if not (self.printflag & PrintModel):
            return
        print(f"\n=== SAT Solution (horizon {maxtime}) ===")
        for i in range(1, numvar + 1):
            if i < len(soln) and soln[i] == 1:
                name = (encoder._prop2name[i]
                        if i < len(encoder._prop2name) else f"var_{i}")
                if name:
                    print(f"  {i}: {name} = TRUE")


def _pretty_action(name: str) -> str:
    """Convert ``move_a_b_c`` to ``(move a b c)``."""
    parts = name.split(CONNECTOR)
    return '(' + ' '.join(parts) + ')'
