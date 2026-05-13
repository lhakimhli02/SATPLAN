"""
live_simulator.py - Live elevator simulation with incremental replanning.

Flow:
  1. Seed passengers → GraphPlan builds initial plan from the initial state.
  2. Each simulation step:
     a. Generate new arrivals stochastically.
     b. If any arrivals: replan from the *current* state (current elevator
        floor + all undelivered passengers including new arrivals + any
        passengers already boarded in the elevator).  The executed prefix is
        kept; only the remaining suffix is replaced.
     c. Execute the next plan step and update state.
"""
from __future__ import annotations

import random
import time as _time
from dataclasses import dataclass, field
from typing import Optional

from elevator_domain import (
    Passenger, PlanStep,
    solve_graphplan, solve_graphplan_from_state,
    ELEVATOR,
)


@dataclass
class SimState:
    lift_floor: int
    passenger_floor: dict[str, int]   # 'p<id>' → floor they are waiting at
    boarded: set[str]                  # 'p<id>' currently in elevator
    delivered: set[str]                # 'p<id>' that reached their destination
    time_step: int = 0


class LiveElevatorSimulator:
    """
    Live elevator simulator with incremental GraphPlan replanning.

    solve_graphplan() is called once for seed passengers.
    solve_graphplan_from_state() is called whenever new passengers arrive,
    replanning from the current elevator position and passenger set — not
    from the original initial state.
    """

    def __init__(
        self,
        num_floors: int = 5,
        arrival_prob: float = 0.3,
        seed_passengers: Optional[list[Passenger]] = None,
        initial_lift_floor: int = 0,
        seed: Optional[int] = None,
    ):
        self.num_floors = num_floors
        self.arrival_prob = arrival_prob
        self.initial_lift_floor = initial_lift_floor
        self.rng = random.Random(seed)
        self._debug = 0

        self.all_passengers: dict[int, Passenger] = {}
        self._next_id = 0

        self.plan_steps: list[PlanStep] = []
        self.current_step = 0

        self.state = SimState(
            lift_floor=initial_lift_floor,
            passenger_floor={},
            boarded=set(),
            delivered=set(),
        )

        # Replanning statistics
        self.replan_count = 0
        self.replan_time = 0.0
        self.total_arrivals = 0

        if seed_passengers:
            for p in seed_passengers:
                self._register_passenger(p)

    def _register_passenger(self, p: Passenger) -> None:
        self.all_passengers[p.id] = p
        self._next_id = max(self._next_id, p.id + 1)
        self.state.passenger_floor[f'p{p.id}'] = p.pickup

    def initialize(self, debug: int = 0) -> bool:
        """
        Solve for seed passengers using GraphPlan (initial solve).
        Returns True on success or if there are no seed passengers.
        """
        self._debug = debug
        seed_pax = list(self.all_passengers.values())
        plan = solve_graphplan(
            self.num_floors, seed_pax, self.initial_lift_floor, debug=debug
        )
        if plan is None:
            return False
        self.plan_steps = plan
        self.current_step = 0
        return True

    def step(self) -> dict:
        """
        Advance simulation by one time step.

        Returns a snapshot dict describing arrivals, replanning, actions taken,
        and current state.
        """
        t = self.state.time_step

        # 1. Generate arrivals and add them to state
        new_arrivals = self._generate_arrivals(t)
        for p in new_arrivals:
            self._register_passenger(p)
            self.total_arrivals += 1

        # 2. Replan from current state if anything new arrived
        replan_triggered = False
        replan_elapsed = 0.0
        if new_arrivals:
            replan_triggered = True
            t0 = _time.time()
            ok = self._replan()
            replan_elapsed = _time.time() - t0
            if not ok:
                # Solver failed (shouldn't happen for well-formed problems);
                # keep the existing remaining plan as a fallback.
                replan_triggered = False

        # 3. Execute next plan step
        actions_taken: list[str] = []
        if self.current_step < len(self.plan_steps):
            plan_step = self.plan_steps[self.current_step]
            actions_taken = list(plan_step.actions)
            self._apply_step(plan_step)
            self.current_step += 1

        self.state.time_step += 1

        return {
            'time': t,
            'arrivals': new_arrivals,
            'replanned': replan_triggered,
            'replan_ms': round(replan_elapsed * 1000, 1),
            'actions': actions_taken,
            'lift_floor': self.state.lift_floor,
            'waiting': dict(self.state.passenger_floor),
            'boarded': set(self.state.boarded),
            'delivered': set(self.state.delivered),
            'plan_remaining': len(self.plan_steps) - self.current_step,
        }

    def _replan(self) -> bool:
        """
        Replan from current state for all undelivered passengers.

        Collects passengers currently waiting (passenger_floor) and those
        already boarded in the elevator, then calls solve_graphplan_from_state()
        starting at the current elevator floor.  The solved plan replaces only
        the unexecuted suffix of self.plan_steps.

        Returns True if a new plan was found.
        """
        waiting_pax = [
            self.all_passengers[int(k[1:])]
            for k in sorted(self.state.passenger_floor)
        ]
        boarded_pax = [
            self.all_passengers[int(k[1:])]
            for k in sorted(self.state.boarded)
        ]

        new_suffix = solve_graphplan_from_state(
            self.num_floors,
            self.state.lift_floor,
            waiting_pax,
            boarded_pax,
            debug=self._debug,
        )

        if new_suffix is None:
            return False

        # Replace the unexecuted suffix; keep the executed prefix for history
        self.plan_steps = self.plan_steps[:self.current_step] + new_suffix
        self.replan_count += 1
        self.replan_time += 0.0   # caller measures and stores separately
        return True

    # ── State application ─────────────────────────────────────────────────

    def _apply_step(self, step: PlanStep) -> None:
        for action in step.actions:
            self._apply_action(action)

    def _apply_action(self, action: str) -> None:
        parts = action.split('_')
        atype = parts[0]

        if atype in ('move-up', 'move-down'):
            self.state.lift_floor = int(parts[3][1:])

        elif atype == 'board':
            pax_key = parts[1]
            self.state.passenger_floor.pop(pax_key, None)
            self.state.boarded.add(pax_key)

        elif atype == 'leave':
            # leave_p{id}_e0_f{floor}
            pax_key = parts[1]
            left_floor = int(parts[3][1:])
            self.state.boarded.discard(pax_key)
            pax = self.all_passengers.get(int(pax_key[1:]))
            if pax is not None and left_floor == pax.dest:
                self.state.delivered.add(pax_key)
            else:
                # Intermediate drop (planner re-routes via this floor).
                # Put them back as waiting so the next replan picks them up.
                self.state.passenger_floor[pax_key] = left_floor
                if pax is not None:
                    self.all_passengers[pax.id] = Passenger(
                        pax.id, pickup=left_floor, dest=pax.dest,
                        arrival_step=pax.arrival_step,
                    )

    # ── Arrival generation ────────────────────────────────────────────────

    def _generate_arrivals(self, time_step: int) -> list[Passenger]:
        arrivals: list[Passenger] = []
        for floor in range(self.num_floors):
            if self.rng.random() < self.arrival_prob:
                other_floors = [f for f in range(self.num_floors) if f != floor]
                if not other_floors:
                    continue
                dest = self.rng.choice(other_floors)
                p = Passenger(
                    id=self._next_id,
                    pickup=floor,
                    dest=dest,
                    arrival_step=time_step,
                )
                arrivals.append(p)
                self._next_id += 1
        return arrivals

    # ── Queries ───────────────────────────────────────────────────────────

    def is_done(self) -> bool:
        return (
            self.current_step >= len(self.plan_steps)
            and not self.state.boarded
            and not self.state.passenger_floor
        )

    def stats(self) -> dict:
        return {
            'total_arrivals': self.total_arrivals,
            'delivered': len(self.state.delivered),
            'still_waiting': len(self.state.passenger_floor),
            'in_elevator': len(self.state.boarded),
            'plan_steps_total': len(self.plan_steps),
            'current_step': self.current_step,
            'replan_count': self.replan_count,
            'replan_time_s': round(self.replan_time, 3),
        }
