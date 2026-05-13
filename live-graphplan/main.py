#!/usr/bin/env python3
"""
main.py - Live elevator simulation demo.

GraphPlan solves for the seed passengers once; all subsequent arrivals are
handled by plan repair (plan_repair.py) without invoking the planner again.

Usage
-----
    python main.py [options]

Options
-------
  --floors N           Number of floors (default: 5)
  --prob P             Per-floor arrival probability per step (default: 0.25)
  --steps N            Total simulation steps to run (default: 20)
  --seed-passengers N  Initial passengers for GraphPlan to solve (default: 2)
  --seed S             Random seed for reproducibility (default: 42)
  --stop-on-done       Stop early once all passengers are delivered
  --debug              Show GraphPlan solver output
"""
from __future__ import annotations

import argparse
import os
import random
import sys

sys.path.insert(0, os.path.dirname(__file__))

from elevator_domain import Passenger
from live_simulator import LiveElevatorSimulator


# ── Formatting helpers ────────────────────────────────────────────────────────

def _pretty_action(action: str) -> str:
    parts = action.split('_')
    atype = parts[0]
    if atype in ('move-up', 'move-down'):
        return f'{atype}({parts[2]}→{parts[3]})'
    if atype == 'board':
        return f'board({parts[1]}@{parts[3]})'
    if atype == 'leave':
        return f'leave({parts[1]}@{parts[3]})'
    return action


def render_frame(result: dict, num_floors: int, all_pax: dict) -> str:
    """ASCII building view + step info."""
    lift = result['lift_floor']
    waiting = result['waiting']     # 'p<id>' → floor int
    boarded = result['boarded']     # set of 'p<id>'
    delivered = result['delivered']

    replan_tag = (f'  ↻ REPLANNED ({result["replan_ms"]} ms)'
                  if result.get('replanned') else '')

    lines: list[str] = []
    lines.append(f"  Step {result['time']:3d}  │  Plan steps remaining: "
                 f"{result['plan_remaining']}{replan_tag}")
    lines.append('  ' + '─' * 52)

    for floor in range(num_floors - 1, -1, -1):
        # Elevator marker; show boarded passengers if elevator is here
        if lift == floor:
            in_car = sorted(boarded)
            car = f'[{",".join(in_car) if in_car else "  "}]'
        else:
            car = '     '

        waiting_here = sorted(k for k, v in waiting.items() if v == floor)
        wait_str = '  wait: ' + ','.join(waiting_here) if waiting_here else ''
        lines.append(f'  F{floor}  {car}{wait_str}')

    lines.append('  ' + '─' * 52)

    if result['arrivals']:
        arr = [f"p{p.id}(F{p.pickup}→F{p.dest})" for p in result['arrivals']]
        lines.append(f'  NEW ARRIVALS : {", ".join(arr)}')

    if result['actions']:
        acts = [_pretty_action(a) for a in result['actions']]
        lines.append(f'  Actions      : {", ".join(acts)}')
    else:
        lines.append('  Actions      : (idle — no plan step)')

    if delivered:
        lines.append(f'  Delivered    : {sorted(delivered)}')

    return '\n'.join(lines)


# ── Entry point ───────────────────────────────────────────────────────────────

def main() -> None:
    parser = argparse.ArgumentParser(
        description='Live elevator simulation with GraphPlan + plan repair',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument('--floors', type=int, default=5,
                        help='Number of floors (default: 5)')
    parser.add_argument('--prob', type=float, default=0.25,
                        help='Per-floor arrival probability per step (default: 0.25)')
    parser.add_argument('--steps', type=int, default=20,
                        help='Total simulation steps (default: 20)')
    parser.add_argument('--seed-passengers', type=int, default=2,
                        help='Initial passengers for GraphPlan (default: 2)')
    parser.add_argument('--seed', type=int, default=42,
                        help='Random seed (default: 42)')
    parser.add_argument('--stop-on-done', action='store_true',
                        help='Stop once all passengers are delivered')
    parser.add_argument('--debug', action='store_true',
                        help='Show GraphPlan solver output')
    args = parser.parse_args()

    # Build seed passengers (separate rng so initial state is reproducible)
    init_rng = random.Random(args.seed)
    seed_pax: list[Passenger] = []
    for i in range(args.seed_passengers):
        pickup = init_rng.randint(0, args.floors - 1)
        dest = init_rng.choice([f for f in range(args.floors) if f != pickup])
        seed_pax.append(Passenger(id=i, pickup=pickup, dest=dest, arrival_step=0))

    # ── Banner ────────────────────────────────────────────────────────────────
    print()
    print('  Live Elevator — GraphPlan + Plan Repair')
    print('  ' + '=' * 60)
    print(f'  Floors: {args.floors}  │  Arrival prob: {args.prob:.2f}  '
          f'│  Seed: {args.seed}')
    print()

    if seed_pax:
        print('  Seed passengers (initial GraphPlan problem):')
        for p in seed_pax:
            print(f'    p{p.id}: F{p.pickup} → F{p.dest}')
    else:
        print('  No seed passengers — starting with empty plan.')
    print()

    # ── Initialise simulator and run GraphPlan once ───────────────────────────
    sim = LiveElevatorSimulator(
        num_floors=args.floors,
        arrival_prob=args.prob,
        seed_passengers=seed_pax,
        initial_lift_floor=0,
        seed=args.seed + 1,
    )

    print('  Running GraphPlan on seed passengers...')
    debug_level = 1 if args.debug else 0
    if not sim.initialize(debug=debug_level):
        print('  ERROR: GraphPlan could not find an initial plan.')
        sys.exit(1)

    print(f'  Initial plan: {len(sim.plan_steps)} steps')
    if sim.plan_steps:
        print('  Initial plan trajectory:')
        floor = sim.initial_lift_floor
        for i, s in enumerate(sim.plan_steps):
            acts = ', '.join(_pretty_action(a) for a in s.actions)
            print(f'    step {i+1:2d}: F{s.floor_before}→F{s.floor_after}  [{acts}]')

    print()
    print(f'  Starting simulation ({args.steps} steps)…')
    print()

    # ── Main simulation loop ──────────────────────────────────────────────────
    for _ in range(args.steps):
        result = sim.step()
        print(render_frame(result, args.floors, sim.all_passengers))
        print()

        if args.stop_on_done and sim.is_done():
            print('  All passengers delivered — stopping early.')
            break

    # ── Summary ───────────────────────────────────────────────────────────────
    s = sim.stats()
    print('  ' + '=' * 60)
    print(f'  Simulation finished after {sim.state.time_step} steps')
    print(f'  Passengers delivered    : {s["delivered"]}')
    print(f'  Still waiting           : {s["still_waiting"]}')
    print(f'  In elevator             : {s["in_elevator"]}')
    print(f'  Total arrivals          : {s["total_arrivals"]}')
    print(f'  Replan count            : {s["replan_count"]}  '
          f'← GraphPlan called from current state each time')
    print(f'  Total plan steps built  : {s["plan_steps_total"]}')
    print()


if __name__ == '__main__':
    main()
