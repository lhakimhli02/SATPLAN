"""
elevator_domain.py - Data structures, PDDL generation, and GraphPlan solve
for the live elevator simulation.
"""
from __future__ import annotations

import os
import sys
import tempfile
from dataclasses import dataclass, field
from typing import Optional

# Add blackbox_python to path so we can reuse PlanningGraph / Planner
_BB_PATH = os.path.abspath(
    os.path.join(os.path.dirname(__file__), '..', 'Blackbox', 'blackbox_python')
)
if _BB_PATH not in sys.path:
    sys.path.insert(0, _BB_PATH)

DOMAIN_FILE = os.path.join(_BB_PATH, 'pddl_problems', 'elevator_domain.pddl')
ELEVATOR = 'e0'


@dataclass
class Passenger:
    id: int
    pickup: int          # pickup floor number (0-indexed)
    dest: int            # destination floor number (0-indexed)
    arrival_step: int = 0


@dataclass
class PlanStep:
    """One parallel time step in the elevator plan."""
    floor_before: int              # elevator floor at START of this step
    floor_after: int               # elevator floor at END of this step
    actions: list[str] = field(default_factory=list)

    @property
    def is_move(self) -> bool:
        return self.floor_before != self.floor_after

    @property
    def is_dwell(self) -> bool:
        return self.floor_before == self.floor_after


def generate_problem_pddl(num_floors: int, passengers: list[Passenger],
                           lift_floor: int = 0) -> str:
    """Generate PDDL problem text for the given initial state."""
    return _build_pddl(num_floors, lift_floor, waiting=passengers, boarded=[])


def generate_problem_pddl_from_state(num_floors: int, lift_floor: int,
                                      waiting: list[Passenger],
                                      boarded: list[Passenger]) -> str:
    """
    Generate PDDL for replanning from a mid-execution state.

    *waiting* passengers get (passenger-at p f_pickup) in :init.
    *boarded* passengers get (boarded p e0) in :init — they are already
    in the elevator and only need a (leave) action to reach their destination.
    Both groups get (passenger-at p f_dest) as goals.
    """
    return _build_pddl(num_floors, lift_floor, waiting=waiting, boarded=boarded)


def _build_pddl(num_floors: int, lift_floor: int,
                waiting: list[Passenger], boarded: list[Passenger]) -> str:
    all_pax = waiting + boarded
    floors = ' '.join(f'f{i}' for i in range(num_floors))
    pax_names = ' '.join(f'p{p.id}' for p in all_pax)
    above = ' '.join(f'(above f{i} f{i+1})' for i in range(num_floors - 1))

    lines = [
        '(define (problem elevators-live)',
        '  (:domain elevators-strips)',
        '  (:objects',
        f'    {floors} - floor',
        f'    {ELEVATOR} - elevator',
    ]
    if all_pax:
        lines.append(f'    {pax_names} - passenger')
    lines += [
        '  )',
        '  (:init',
        f'    {above}',
        f'    (lift-at {ELEVATOR} f{lift_floor})',
    ]
    for p in waiting:
        lines.append(f'    (passenger-at p{p.id} f{p.pickup})')
    for p in boarded:
        lines.append(f'    (boarded p{p.id} {ELEVATOR})')
    lines += ['  )', '  (:goal', '    (and']
    for p in all_pax:
        lines.append(f'      (passenger-at p{p.id} f{p.dest})')
    lines += ['    )', '  )', ')']
    return '\n'.join(lines)


def solve_graphplan_from_state(num_floors: int, lift_floor: int,
                               waiting: list[Passenger],
                               boarded: list[Passenger],
                               max_steps: int = 50,
                               debug: int = 0) -> Optional[list[PlanStep]]:
    """
    Replan from a mid-execution state.

    *lift_floor* is the elevator's current floor.
    *waiting*   passengers are at their pickup floor, not yet boarded.
    *boarded*   passengers are already in the elevator.

    Returns a fresh list[PlanStep] from the current state onward,
    or None if no plan is found within max_steps.
    """
    all_pax = waiting + boarded
    if not all_pax:
        return []

    from graphplan import PlanningGraph
    from planner import Planner
    from data_structures import SolverSpec, Anysat, Sat

    fd, problem_file = tempfile.mkstemp(suffix='.pddl', prefix='live_replan_')
    os.close(fd)
    try:
        with open(problem_file, 'w') as f:
            f.write(generate_problem_pddl_from_state(
                num_floors, lift_floor, waiting, boarded))

        graph = PlanningGraph()
        graph.debug_flag = debug
        graph.load(DOMAIN_FILE, problem_file)
        graph.process_data()
        graph.create_graph(max_steps, auto_stop=False)

        planner = Planner(
            graph=graph,
            solver_specs=[SolverSpec(solver_name='cadical', solver_type=Anysat)],
            debug=debug,
            noopt=True,
            do_justify=False,
        )

        for horizon in range(1, max_steps + 1):
            if horizon >= len(graph.fact_table):
                break
            # Only attempt a solve when ALL goals are reachable and non-mutex.
            # Without this guard, the SAT solver returns Sat for whichever
            # goals happen to be reachable at small horizons, yielding an
            # incomplete plan that ignores the rest of the passengers.
            if not graph.can_stop(horizon):
                continue
            if planner.do_plan(horizon) == Sat:
                return _extract_steps(graph, horizon, lift_floor)
        return None
    finally:
        os.unlink(problem_file)


def solve_graphplan(num_floors: int, passengers: list[Passenger],
                    lift_floor: int = 0, max_steps: int = 50,
                    debug: int = 0) -> Optional[list[PlanStep]]:
    """
    Run GraphPlan (BlackBox) on the given initial state and passengers.

    Returns a list of PlanStep on success, [] if no passengers (trivially done),
    or None if no plan found within max_steps.

    This is the ONE place where the full planner is called. Subsequent passenger
    arrivals are handled by plan_repair.py without calling this function again.
    """
    if not passengers:
        return []

    from graphplan import PlanningGraph
    from planner import Planner
    from data_structures import SolverSpec, Anysat, Sat

    fd, problem_file = tempfile.mkstemp(suffix='.pddl', prefix='live_elev_')
    os.close(fd)
    try:
        with open(problem_file, 'w') as f:
            f.write(generate_problem_pddl(num_floors, passengers, lift_floor))

        graph = PlanningGraph()
        graph.debug_flag = debug
        graph.load(DOMAIN_FILE, problem_file)
        graph.process_data()
        graph.create_graph(max_steps, auto_stop=False)

        planner = Planner(
            graph=graph,
            solver_specs=[SolverSpec(solver_name='cadical', solver_type=Anysat)],
            debug=debug,
            noopt=True,
            do_justify=False,
        )

        for horizon in range(1, max_steps + 1):
            if horizon >= len(graph.fact_table):
                break
            if not graph.can_stop(horizon):
                continue
            if planner.do_plan(horizon) == Sat:
                return _extract_steps(graph, horizon, lift_floor)
        return None
    finally:
        os.unlink(problem_file)


def _extract_steps(graph, maxtime: int, initial_floor: int) -> list[PlanStep]:
    """
    Extract a PlanStep list from a solved PlanningGraph.

    In the elevator domain each time step is either:
      - a move step (floor_before != floor_after) with exactly one move action
      - a dwell step (floor_before == floor_after) with board/leave actions

    Board and move are mutex in GraphPlan (move deletes the precondition of
    board at the source floor), so they are always in separate steps.
    """
    steps: list[PlanStep] = []
    current_floor = initial_floor

    for t in range(maxtime):
        actions: list[str] = []
        next_floor = current_floor

        for op in graph.op_table[t]:
            if not op.used or op.is_noop:
                continue
            name = op.name
            parts = name.split('_')
            atype = parts[0]
            if atype in ('move-up', 'move-down'):
                next_floor = int(parts[3][1:])   # 'f3' → 3
            actions.append(name)

        if actions:  # skip empty (all-noop) time steps
            steps.append(PlanStep(
                floor_before=current_floor,
                floor_after=next_floor,
                actions=actions,
            ))
        current_floor = next_floor

    return steps
