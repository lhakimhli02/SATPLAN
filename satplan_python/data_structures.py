"""
data_structures.py - Minimal status codes and solver spec for SATplan.
"""

from dataclasses import dataclass, field

# SAT solver return values
Unsat = 0
Sat = 1
Timeout = 2
Failure = 3

# Solver type identifiers
Anysat = 0

# Print masks
PrintLit = 1
PrintCNF = 2
PrintModel = 16

CONNECTOR = '_'


@dataclass
class SolverSpec:
    """Solver specification."""
    solver_name: str = "cadical"
    solver_type: int = Anysat
    maxsec: int = 0
    maxit: int = 0
    argv: list = field(default_factory=list)
