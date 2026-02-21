"""
sat_interface.py - Interface to SAT solvers via PySAT.

Replaces: sat_solver.cpp

Uses the python-sat (PySAT) library for SAT solving. No C++ compilation
or external binaries required.

Available solvers:
  - cadical  (CaDiCaL 1.9.5) - default, top SAT competition performer
  - glucose  (Glucose 4.2)   - strong on industrial benchmarks
  - maple   (MapleChrono)    - SAT competition 2018 winner
  - minisat (MinisatGH)      - classic CDCL solver
  - kissat  (external)       - state-of-the-art competition solver
  - walksat (built-in)       - stochastic local search (incomplete)
  - dpll   (built-in)       - pure Python DPLL with Jeroslow-Wang heuristic

Install: pip install python-sat
"""

from __future__ import annotations
import os
import subprocess
import sys
import tempfile
from typing import Optional

from pysat.solvers import Cadical195, Glucose42, MapleChrono, MinisatGH

from data_structures import Sat, Unsat, Timeout, Failure


# ── Solver dispatch ──────────────────────────────────────────────────────────

SOLVER_CLASSES = {
    'cadical': Cadical195,
    'cd195': Cadical195,
    'glucose': Glucose42,
    'g42': Glucose42,
    'maple': MapleChrono,
    'mcb': MapleChrono,
    'minisat': MinisatGH,
    'mgh': MinisatGH,
}

DEFAULT_SOLVER = 'cadical'


class IncrementalSATSolver:
    """Stateful incremental SAT session backed by a PySAT solver instance."""

    def __init__(self, solver_name: str = DEFAULT_SOLVER, debug: int = 0):
        key = (solver_name or DEFAULT_SOLVER).lower()
        solver_cls = SOLVER_CLASSES.get(key)
        if solver_cls is None:
            raise ValueError(f"Unknown solver '{solver_name}'")
        self.solver_name = key
        self.solver_cls = solver_cls
        self.debug = debug
        self.solver = solver_cls()

    def reset(self):
        """Drop all clauses and recreate the underlying SAT solver."""
        self.delete()
        self.solver = self.solver_cls()

    def add_clauses(self, clauses: list[list[int]]):
        for clause in clauses:
            self.solver.add_clause(clause)

    def solve(self, numvar: int, maxtime: int = 0,
              assumptions: Optional[list[int]] = None) -> tuple[int, list[int]]:
        """Solve with optional assumptions and return (status, 1-indexed model)."""
        assumps = assumptions if assumptions is not None else []
        soln = [0] * (numvar + 1)
        try:
            before = self.solver.accum_stats().copy() if hasattr(self.solver, 'accum_stats') else None
            if maxtime > 0:
                try:
                    result = self.solver.solve_limited(expect_interrupt=True,
                                                      timer=maxtime,
                                                      assumptions=assumps)
                except TypeError:
                    # Some wrappers do not accept timer/assumptions in solve_limited.
                    try:
                        result = self.solver.solve_limited(expect_interrupt=True,
                                                          assumptions=assumps)
                    except TypeError:
                        result = self.solver.solve_limited(expect_interrupt=True)
            else:
                result = self.solver.solve(assumptions=assumps)

            if result is True:
                model = self.solver.get_model()
                if model:
                    for lit in model:
                        var = abs(lit)
                        if 1 <= var <= numvar:
                            soln[var] = 1 if lit > 0 else 0
                if self.debug >= 1 and before is not None:
                    after = self.solver.accum_stats().copy()
                    delta = {k: int(after.get(k, 0)) - int(before.get(k, 0))
                             for k in after.keys()}
                    print("  SAT search: "
                          f"decisions={delta.get('decisions', 0)} "
                          f"conflicts={delta.get('conflicts', 0)} "
                          f"propagations={delta.get('propagations', 0)}")
                return Sat, soln
            if result is False:
                if self.debug >= 1 and before is not None:
                    after = self.solver.accum_stats().copy()
                    delta = {k: int(after.get(k, 0)) - int(before.get(k, 0))
                             for k in after.keys()}
                    print("  SAT search: "
                          f"decisions={delta.get('decisions', 0)} "
                          f"conflicts={delta.get('conflicts', 0)} "
                          f"propagations={delta.get('propagations', 0)}")
                return Unsat, soln
            if self.debug >= 1 and before is not None:
                after = self.solver.accum_stats().copy()
                delta = {k: int(after.get(k, 0)) - int(before.get(k, 0))
                         for k in after.keys()}
                print("  SAT search: "
                      f"decisions={delta.get('decisions', 0)} "
                      f"conflicts={delta.get('conflicts', 0)} "
                      f"propagations={delta.get('propagations', 0)}")
            return Timeout, soln
        except Exception as e:
            print(f"  SAT solver error: {e}", file=sys.stderr)
            return Failure, soln

    def delete(self):
        if self.solver is not None:
            try:
                self.solver.delete()
            finally:
                self.solver = None


def _solve_with_pysat(solver_cls, clauses: list[list[int]], numvar: int,
                      numclause: int, maxtime: int = 0,
                      debug: int = 0) -> tuple[int, list[int]]:
    """Run a PySAT solver on the given CNF clauses.

    Returns (status, soln) where soln is a 1-indexed assignment array:
    soln[v] = 1 if variable v is true, 0 if false.
    """
    soln = [0] * (numvar + 1)

    try:
        solver = solver_cls()
        for clause in clauses:
            solver.add_clause(clause)
        before = solver.accum_stats().copy() if hasattr(solver, 'accum_stats') else None

        if maxtime > 0:
            result = solver.solve_limited(expect_interrupt=True,
                                          timer=maxtime)
        else:
            result = solver.solve()

        if result is True:
            model = solver.get_model()
            if model:
                for lit in model:
                    var = abs(lit)
                    if 1 <= var <= numvar:
                        soln[var] = 1 if lit > 0 else 0
            if debug >= 1 and before is not None:
                after = solver.accum_stats().copy()
                delta = {k: int(after.get(k, 0)) - int(before.get(k, 0))
                         for k in after.keys()}
                print("  SAT search: "
                      f"decisions={delta.get('decisions', 0)} "
                      f"conflicts={delta.get('conflicts', 0)} "
                      f"propagations={delta.get('propagations', 0)}")
            solver.delete()
            return Sat, soln
        elif result is False:
            if debug >= 1 and before is not None:
                after = solver.accum_stats().copy()
                delta = {k: int(after.get(k, 0)) - int(before.get(k, 0))
                         for k in after.keys()}
                print("  SAT search: "
                      f"decisions={delta.get('decisions', 0)} "
                      f"conflicts={delta.get('conflicts', 0)} "
                      f"propagations={delta.get('propagations', 0)}")
            solver.delete()
            return Unsat, soln
        else:
            if debug >= 1 and before is not None:
                after = solver.accum_stats().copy()
                delta = {k: int(after.get(k, 0)) - int(before.get(k, 0))
                         for k in after.keys()}
                print("  SAT search: "
                      f"decisions={delta.get('decisions', 0)} "
                      f"conflicts={delta.get('conflicts', 0)} "
                      f"propagations={delta.get('propagations', 0)}")
            solver.delete()
            return Timeout, soln

    except Exception as e:
        print(f"  SAT solver error: {e}", file=sys.stderr)
        return Failure, soln


# ── Public API (matches original interface used by planner.py) ───────────────

def bb_satsolve_cadical(clauses: list[list[int]], numvar: int, numclause: int,
                        maxtime: int = 0, extra_args: list[str] | None = None,
                        debug: int = 0) -> tuple[int, list[int]]:
    """Solve with CaDiCaL 1.9.5."""
    if debug >= 2:
        print(f"  [cadical] {numvar} vars, {numclause} clauses")
    return _solve_with_pysat(Cadical195, clauses, numvar, numclause,
                             maxtime, debug)


def bb_satsolve_glucose(clauses: list[list[int]], numvar: int, numclause: int,
                        maxtime: int = 0, extra_args: list[str] | None = None,
                        debug: int = 0) -> tuple[int, list[int]]:
    """Solve with Glucose 4.2."""
    if debug >= 2:
        print(f"  [glucose] {numvar} vars, {numclause} clauses")
    return _solve_with_pysat(Glucose42, clauses, numvar, numclause,
                             maxtime, debug)


def bb_satsolve_maple(clauses: list[list[int]], numvar: int, numclause: int,
                      maxtime: int = 0, extra_args: list[str] | None = None,
                      debug: int = 0) -> tuple[int, list[int]]:
    """Solve with MapleChrono (MapleLCMDistChronoBT)."""
    if debug >= 2:
        print(f"  [maple] {numvar} vars, {numclause} clauses")
    return _solve_with_pysat(MapleChrono, clauses, numvar, numclause,
                             maxtime, debug)


def bb_satsolve_minisat(clauses: list[list[int]], numvar: int, numclause: int,
                        maxtime: int = 0, extra_args: list[str] | None = None,
                        debug: int = 0) -> tuple[int, list[int]]:
    """Solve with MinisatGH (MiniSat GitHub fork via PySAT)."""
    if debug >= 2:
        print(f"  [minisat] {numvar} vars, {numclause} clauses")
    return _solve_with_pysat(MinisatGH, clauses, numvar, numclause,
                             maxtime, debug)


# ── Kissat (external binary via DIMACS) ──────────────────────────────────────

def _find_kissat_binary() -> str | None:
    """Locate the kissat binary on the system."""
    import shutil
    # Check PATH first
    path = shutil.which('kissat')
    if path:
        return path
    # Check passagemath-kissat bundled binary via importlib
    try:
        import importlib.util
        spec = importlib.util.find_spec('sage_wheels')
        if spec and spec.submodule_search_locations:
            for loc in spec.submodule_search_locations:
                candidate = os.path.join(loc, 'bin', 'kissat')
                if os.path.isfile(candidate) and os.access(candidate, os.X_OK):
                    return candidate
    except Exception:
        pass
    # Fallback: scan sys.path for sage_wheels/bin/kissat
    for sp in sys.path:
        candidate = os.path.join(sp, 'sage_wheels', 'bin', 'kissat')
        if os.path.isfile(candidate) and os.access(candidate, os.X_OK):
            return candidate
    # Walk up from this file's directory looking for .venv/lib/**/sage_wheels/bin/kissat
    anchor = os.path.dirname(os.path.abspath(__file__))
    for _ in range(5):
        venv = os.path.join(anchor, '.venv')
        if os.path.isdir(venv):
            lib = os.path.join(venv, 'lib')
            if os.path.isdir(lib):
                for root, dirs, files in os.walk(lib):
                    if root.endswith(os.sep + 'bin') and 'kissat' in files:
                        candidate = os.path.join(root, 'kissat')
                        if os.access(candidate, os.X_OK):
                            return candidate
        anchor = os.path.dirname(anchor)
    return None


class KissatSolver:
    """Wrapper that calls the kissat binary on a DIMACS CNF temp file."""

    _binary_missing_warned = False
    _binary_path: str | None = None
    _binary_searched = False

    def __init__(self, debug: int = 0):
        self.debug = debug

    @classmethod
    def _get_binary(cls) -> str | None:
        if not cls._binary_searched:
            cls._binary_path = _find_kissat_binary()
            cls._binary_searched = True
        return cls._binary_path

    def solve(self, clauses: list[list[int]], numvar: int, numclause: int,
              maxtime: int = 0) -> tuple[int, list[int]]:
        soln = [0] * (numvar + 1)

        kissat_bin = self._get_binary()
        if kissat_bin is None:
            if not KissatSolver._binary_missing_warned:
                print("  Kissat binary not found. Install with: pip install passagemath-kissat",
                      file=sys.stderr)
                KissatSolver._binary_missing_warned = True
            return Failure, soln

        # Write DIMACS CNF to a temp file
        try:
            fd, cnf_path = tempfile.mkstemp(suffix='.cnf')
            with os.fdopen(fd, 'w') as f:
                f.write(f"p cnf {numvar} {len(clauses)}\n")
                for clause in clauses:
                    f.write(' '.join(str(lit) for lit in clause) + ' 0\n')
        except Exception as e:
            print(f"  Kissat error writing CNF: {e}", file=sys.stderr)
            return Failure, soln

        try:
            cmd = [kissat_bin, '--quiet', cnf_path]
            if maxtime > 0:
                cmd = [kissat_bin, '--quiet', f'--time={maxtime}', cnf_path]

            if self.debug >= 2:
                print(f"  Running: {' '.join(cmd)}")

            proc = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=maxtime + 10 if maxtime > 0 else None,
            )

            # Kissat exit codes: 10 = SAT, 20 = UNSAT, other = unknown/timeout
            if proc.returncode == 10:
                # Parse model from stdout (lines starting with 'v')
                for line in proc.stdout.splitlines():
                    line = line.strip()
                    if line.startswith('v '):
                        for tok in line[2:].split():
                            lit = int(tok)
                            if lit == 0:
                                break
                            var = abs(lit)
                            if 1 <= var <= numvar:
                                soln[var] = 1 if lit > 0 else 0
                return Sat, soln
            elif proc.returncode == 20:
                return Unsat, soln
            else:
                return Timeout, soln

        except subprocess.TimeoutExpired:
            return Timeout, soln
        except Exception as e:
            print(f"  Kissat error: {e}", file=sys.stderr)
            return Failure, soln
        finally:
            try:
                os.unlink(cnf_path)
            except OSError:
                pass


def bb_satsolve_kissat(clauses: list[list[int]], numvar: int, numclause: int,
                       maxtime: int = 0, extra_args: list[str] | None = None,
                       debug: int = 0) -> tuple[int, list[int]]:
    """Solve with Kissat (external binary)."""
    if debug >= 2:
        print(f"  [kissat] {numvar} vars, {numclause} clauses")
    solver = KissatSolver(debug=debug)
    return solver.solve(clauses, numvar, numclause, maxtime)


# ── WalkSAT (external C binary via DIMACS) ───────────────────────────────────

def _find_walksat_binary() -> str | None:
    """Locate the walksat binary on the system."""
    import shutil
    path = shutil.which('walksat')
    if path:
        return path
    for candidate in [
        os.path.join(os.path.dirname(__file__), 'walksat'),
        os.path.expanduser('~/bin/walksat'),
        '/usr/local/bin/walksat',
    ]:
        if os.path.isfile(candidate) and os.access(candidate, os.X_OK):
            return candidate
    return None


class WalkSATSolver:
    """WalkSAT solver that calls the Kautz C binary.

    Requires the walksat binary on PATH. Build from:
    https://gitlab.com/HenryKautz/Walksat

    WalkSAT is incomplete: it can find satisfying assignments but cannot
    prove unsatisfiability. Returns Timeout (not Unsat) when it fails.
    """

    _binary_path: str | None = None
    _binary_searched = False

    def __init__(self, max_flips: int = 5000000, max_restarts: int = 100,
                 noise: float = 0.4, debug: int = 0):
        self.max_flips = max_flips
        self.max_restarts = max_restarts
        self.noise = noise
        self.debug = debug

    @classmethod
    def _get_binary(cls) -> str | None:
        if not cls._binary_searched:
            cls._binary_path = _find_walksat_binary()
            cls._binary_searched = True
        return cls._binary_path

    def solve(self, clauses: list[list[int]], numvar: int, numclause: int,
              maxtime: int = 0) -> tuple[int, list[int]]:
        soln = [0] * (numvar + 1)

        binary = self._get_binary()
        if binary is None:
            print("  Error: walksat binary not found. "
                  "Build from https://gitlab.com/HenryKautz/Walksat "
                  "and place on PATH.", file=sys.stderr)
            return Failure, soln

        # Write DIMACS CNF
        try:
            fd, cnf_path = tempfile.mkstemp(suffix='.cnf')
            with os.fdopen(fd, 'w') as f:
                f.write(f"p cnf {numvar} {len(clauses)}\n")
                for clause in clauses:
                    f.write(' '.join(str(lit) for lit in clause) + ' 0\n')
        except Exception as e:
            print(f"  WalkSAT error writing CNF: {e}", file=sys.stderr)
            return Failure, soln

        try:
            cmd = [
                binary,
                '-solcnf',
                '-cutoff', str(self.max_flips),
                '-restart', str(self.max_restarts),
                '-numsol', '1',
                '-noise', str(self.noise),
                cnf_path,
            ]

            timeout_sec = maxtime if maxtime > 0 else None

            if self.debug >= 2:
                print(f"  Running: {' '.join(cmd)}")

            proc = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=timeout_sec + 5 if timeout_sec else None,
            )

            found = False
            for line in proc.stdout.splitlines():
                line = line.strip()
                # WalkSAT v57 outputs one literal per line: "v 1", "v -3"
                # Older versions may output all on one line: "v 1 -2 3 0"
                if line.startswith('v '):
                    found = True
                    for tok in line[2:].split():
                        lit = int(tok)
                        if lit == 0:
                            continue
                        var = abs(lit)
                        if 1 <= var <= numvar:
                            soln[var] = 1 if lit > 0 else 0

            if found:
                return Sat, soln
            return Timeout, soln

        except subprocess.TimeoutExpired:
            return Timeout, soln
        except Exception as e:
            print(f"  WalkSAT error: {e}", file=sys.stderr)
            return Failure, soln
        finally:
            try:
                os.unlink(cnf_path)
            except OSError:
                pass


def bb_satsolve_walksat(clauses: list[list[int]], numvar: int, numclause: int,
                        maxtime: int = 0, extra_args: list[str] | None = None,
                        debug: int = 0) -> tuple[int, list[int]]:
    """Solve with WalkSAT (external C binary)."""
    if debug >= 2:
        print(f"  [walksat] {numvar} vars, {numclause} clauses")
    solver = WalkSATSolver(debug=debug)
    return solver.solve(clauses, numvar, numclause, maxtime)


# ── DPLL (pure Python, ported from marcmelis/dpll-sat) ──────────────────────

class DPLLSolver:
    """Pure Python DPLL SAT solver with Jeroslow-Wang branching heuristic.

    Ported from https://github.com/marcmelis/dpll-sat (MIT license).
    No clause learning — pure backtracking + unit propagation.
    """

    def __init__(self, debug: int = 0):
        self.debug = debug
        self.decisions = 0
        self.propagations = 0

    @staticmethod
    def _bcp(formula: list[list[int]], unit: int) -> list[list[int]] | int:
        """Boolean constraint propagation: assign *unit* true."""
        modified = []
        for clause in formula:
            if unit in clause:
                continue  # clause satisfied
            if -unit in clause:
                new_clause = [x for x in clause if x != -unit]
                if not new_clause:
                    return -1  # conflict
                modified.append(new_clause)
            else:
                modified.append(clause)
        return modified

    def _unit_propagation(self, formula):
        """Iteratively propagate unit clauses."""
        assignment = []
        unit_clauses = [c for c in formula if len(c) == 1]
        while unit_clauses:
            unit = unit_clauses[0][0]
            formula = self._bcp(formula, unit)
            assignment.append(unit)
            self.propagations += 1
            if formula == -1:
                return -1, []
            if not formula:
                return formula, assignment
            unit_clauses = [c for c in formula if len(c) == 1]
        return formula, assignment

    @staticmethod
    def _jeroslow_wang(formula: list[list[int]]) -> int:
        """Jeroslow-Wang branching heuristic: pick the literal with highest
        weighted frequency, weighting shorter clauses exponentially more."""
        counter: dict[int, float] = {}
        for clause in formula:
            w = 2.0 ** -len(clause)
            for lit in clause:
                counter[lit] = counter.get(lit, 0.0) + w
        return max(counter, key=counter.get)

    def _backtrack(self, formula, assignment):
        formula, unit_assignment = self._unit_propagation(formula)
        assignment = assignment + unit_assignment
        if formula == -1:
            return []
        if not formula:
            return assignment

        self.decisions += 1
        variable = self._jeroslow_wang(formula)

        solution = self._backtrack(self._bcp(formula, variable),
                                   assignment + [variable])
        if not solution:
            solution = self._backtrack(self._bcp(formula, -variable),
                                       assignment + [-variable])
        return solution

    def solve(self, clauses: list[list[int]], numvar: int,
              numclause: int, maxtime: int = 0) -> tuple[int, list[int]]:
        soln = [0] * (numvar + 1)
        self.decisions = 0
        self.propagations = 0

        # Deep copy clauses to avoid mutation.
        formula = [list(c) for c in clauses]

        solution = self._backtrack(formula, [])

        if self.debug >= 1:
            print(f"  DPLL search: decisions={self.decisions} "
                  f"propagations={self.propagations}")

        if solution:
            for lit in solution:
                var = abs(lit)
                if 1 <= var <= numvar:
                    soln[var] = 1 if lit > 0 else 0
            return Sat, soln
        return Unsat, soln


def bb_satsolve_dpll(clauses: list[list[int]], numvar: int, numclause: int,
                     maxtime: int = 0, extra_args: list[str] | None = None,
                     debug: int = 0) -> tuple[int, list[int]]:
    """Solve with pure Python DPLL (Jeroslow-Wang heuristic)."""
    if debug >= 2:
        print(f"  [dpll] {numvar} vars, {numclause} clauses")
    solver = DPLLSolver(debug=debug)
    return solver.solve(clauses, numvar, numclause, maxtime)
