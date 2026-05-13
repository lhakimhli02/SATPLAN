"""
plan_repair.py - Plan repair for dynamically arriving passengers.

No replanning (no GraphPlan calls). Strategy:

  1. Scan the remaining plan for a *dwell step* (no move) where the elevator
     is already at the pickup floor.
  2. If found, also scan after that for a dwell step at the destination floor.
  3. If both found → insert board/leave into those existing steps (0 new steps).
  4. If only the board point is found → insert board there, then append
     move-to-dest + leave at the end (partial insertion).
  5. If neither found → append a full detour: move-to-pickup, board,
     move-to-dest, leave.

A "dwell step" is one where floor_before == floor_after (elevator stays put).
Board/leave and move actions are always in separate time steps in the elevator
domain (GraphPlan marks them mutex), so inserting into a dwell step is always
valid.
"""
from __future__ import annotations

from elevator_domain import PlanStep, Passenger, ELEVATOR


def repair_for_passenger(
    steps: list[PlanStep],
    current_step: int,
    passenger: Passenger,
    initial_floor: int = 0,
) -> tuple[bool, int]:
    """
    Repair *steps* in-place so that *passenger* gets served.

    Parameters
    ----------
    steps        : mutable plan (may be extended)
    current_step : index of the next step yet to be executed
    passenger    : newly arrived passenger
    initial_floor: elevator floor before any step (used when steps is empty)

    Returns
    -------
    (no_new_steps, steps_added)
      no_new_steps=True  → repair used only existing dwell steps
      no_new_steps=False → detour was appended; steps_added new steps added
    """
    if passenger.pickup == passenger.dest:
        return True, 0   # trivially delivered

    pid = passenger.id
    pickup, dest = passenger.pickup, passenger.dest

    board_idx = _find_dwell(steps, current_step, pickup)

    if board_idx is not None:
        steps[board_idx].actions.append(
            f'board_p{pid}_{ELEVATOR}_f{pickup}'
        )
        leave_idx = _find_dwell(steps, board_idx + 1, dest)
        if leave_idx is not None:
            # Best case: board AND leave fit into existing trajectory
            steps[leave_idx].actions.append(
                f'leave_p{pid}_{ELEVATOR}_f{dest}'
            )
            return True, 0
        # Board inserted; append only the leave portion
        end_floor = steps[-1].floor_after if steps else initial_floor
        added = _append_move_and_leave(steps, end_floor, passenger)
        return False, added

    # No board point in existing trajectory — append full detour
    end_floor = steps[-1].floor_after if steps else initial_floor
    added = _append_detour(steps, end_floor, passenger)
    return False, added


# ── Internal helpers ──────────────────────────────────────────────────────────

def _find_dwell(steps: list[PlanStep], from_idx: int, floor: int) -> int | None:
    """Return index of first dwell step at *floor* starting from *from_idx*."""
    for i in range(from_idx, len(steps)):
        s = steps[i]
        if s.floor_before == floor and s.floor_after == floor:
            return i
    return None


def _append_move_and_leave(steps: list[PlanStep], start_floor: int,
                            passenger: Passenger) -> int:
    """Append move steps to dest then a dwell-leave step. Returns steps added."""
    added = 0
    current = start_floor
    dest = passenger.dest
    pid = passenger.id

    while current != dest:
        nxt = current + (1 if dest > current else -1)
        mv = (f'move-up_{ELEVATOR}_f{current}_f{nxt}' if nxt > current
              else f'move-down_{ELEVATOR}_f{current}_f{nxt}')
        steps.append(PlanStep(floor_before=current, floor_after=nxt, actions=[mv]))
        current = nxt
        added += 1

    steps.append(PlanStep(
        floor_before=dest, floor_after=dest,
        actions=[f'leave_p{pid}_{ELEVATOR}_f{dest}'],
    ))
    return added + 1


def _append_detour(steps: list[PlanStep], start_floor: int,
                   passenger: Passenger) -> int:
    """Append move-to-pickup, board, move-to-dest, leave. Returns steps added."""
    pid = passenger.id
    pickup, dest = passenger.pickup, passenger.dest
    added = 0
    current = start_floor

    # Move to pickup
    while current != pickup:
        nxt = current + (1 if pickup > current else -1)
        mv = (f'move-up_{ELEVATOR}_f{current}_f{nxt}' if nxt > current
              else f'move-down_{ELEVATOR}_f{current}_f{nxt}')
        steps.append(PlanStep(floor_before=current, floor_after=nxt, actions=[mv]))
        current = nxt
        added += 1

    # Dwell at pickup to board
    steps.append(PlanStep(
        floor_before=pickup, floor_after=pickup,
        actions=[f'board_p{pid}_{ELEVATOR}_f{pickup}'],
    ))
    added += 1

    # Move to dest
    while current != dest:
        nxt = current + (1 if dest > current else -1)
        mv = (f'move-up_{ELEVATOR}_f{current}_f{nxt}' if nxt > current
              else f'move-down_{ELEVATOR}_f{current}_f{nxt}')
        steps.append(PlanStep(floor_before=current, floor_after=nxt, actions=[mv]))
        current = nxt
        added += 1

    # Dwell at dest to leave
    steps.append(PlanStep(
        floor_before=dest, floor_after=dest,
        actions=[f'leave_p{pid}_{ELEVATOR}_f{dest}'],
    ))
    return added + 1
