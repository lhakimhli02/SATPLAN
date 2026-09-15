"""
pddl_generator.py  —  Generate PDDL problem strings for each domain.
"""
from __future__ import annotations
import string

_ALPHA = list(string.ascii_uppercase)   # A-Z


def _block_names(n: int) -> list[str]:
    return _ALPHA[:n] if n <= 26 else [f'b{i+1}' for i in range(n)]


def gen_blocksworld_pddl(n_blocks: int) -> str:
    blocks = _block_names(n_blocks)
    objs   = ' '.join(blocks)
    clears = ' '.join(f'(CLEAR {b})' for b in blocks)
    tables = ' '.join(f'(ONTABLE {b})' for b in blocks)
    # Goal: build one big tower  A on B on C on … (A at top, last block at bottom)
    goal   = ' '.join(f'(ON {blocks[i]} {blocks[i+1]})' for i in range(n_blocks - 1))
    return f"""(define (problem BLOCKS-CUSTOM-{n_blocks})
  (:domain BLOCKS)
  (:objects {objs})
  (:init {clears}
         {tables}
         (HANDEMPTY))
  (:goal (and {goal})))"""


def gen_ferry_pddl(n_cars: int) -> str:
    cars = [f'c{i+1}' for i in range(n_cars)]
    objs = 'left right ' + ' '.join(cars)
    init = '(at-ferry left) (empty)\n    ' + ' '.join(f'(at {c} left)' for c in cars)
    goal = '\n      '.join(f'(at {c} right)' for c in cars)
    return f"""(define (problem ferry-{n_cars}cars)
  (:domain ferry)
  (:objects {objs})
  (:init
    {init})
  (:goal
    (and
      {goal})))"""


def gen_hanoi_pddl(n_discs: int) -> str:
    discs = [f'd{i+1}' for i in range(n_discs)]   # d1=top/smallest, dn=bottom/largest
    objs  = ' '.join(discs) + ' peg1 peg2 peg3'

    on_facts = ' '.join(f'(on {discs[i]} {discs[i+1]})' for i in range(n_discs - 1))
    on_facts += f' (on {discs[-1]} peg1)'
    clear_facts = f'(clear {discs[0]}) (clear peg2) (clear peg3)'

    smaller = []
    for i in range(n_discs):
        for j in range(i + 1, n_discs):
            smaller.append(f'(smaller {discs[i]} {discs[j]})')
        for peg in ('peg1', 'peg2', 'peg3'):
            smaller.append(f'(smaller {discs[i]} {peg})')
    smaller_str = '\n    '.join(smaller)

    goal_on = ' '.join(f'(on {discs[i]} {discs[i+1]})' for i in range(n_discs - 1))
    goal_on += f' (on {discs[-1]} peg3)'

    return f"""(define (problem hanoi-{n_discs}disc)
  (:domain hanoi)
  (:objects {objs})
  (:init
    {on_facts}
    {clear_facts}
    {smaller_str})
  (:goal
    (and {goal_on})))"""


def gen_elevator_pddl(n_passengers: int, n_elevators: int, n_floors: int) -> str:
    floors     = [f'f{i}' for i in range(n_floors)]
    elevators  = [f'e{i}' for i in range(n_elevators)]
    passengers = [f'p{i}' for i in range(n_passengers)]

    above = ' '.join(f'(above {floors[i]} {floors[i+1]})' for i in range(n_floors - 1))

    # Spread elevators: first at f0, last at top, middle at mid (if 3)
    positions = [floors[0], floors[-1], floors[n_floors // 2]]
    lift_init = ' '.join(f'(lift-at {elevators[i]} {positions[i]})' for i in range(n_elevators))

    # Passengers: round-robin starting floors; goal = shift by half
    shift      = max(1, n_floors // 2)
    p_start    = [floors[i % n_floors] for i in range(n_passengers)]
    p_goal     = [floors[(i + shift) % n_floors] for i in range(n_passengers)]
    pass_init  = ' '.join(f'(passenger-at {passengers[i]} {p_start[i]})'
                          for i in range(n_passengers))
    pass_goal  = '\n      '.join(f'(passenger-at {passengers[i]} {p_goal[i]})'
                                  for i in range(n_passengers))

    obj_block = (f'    {" ".join(floors)} - floor\n'
                 f'    {" ".join(elevators)} - elevator\n'
                 f'    {" ".join(passengers)} - passenger')

    return f"""(define (problem elevators-custom-{n_passengers}p-{n_elevators}e)
  (:domain elevators-strips)
  (:objects
{obj_block}
  )
  (:init
    {above}
    {lift_init}
    {pass_init}
  )
  (:goal
    (and
      {pass_goal}
    )
  )
)"""


def describe(domain: str, params: dict) -> str:
    """Short human-readable description of the generated problem."""
    if domain == "Blocksworld":
        n = params["blocks"]
        names = _block_names(n)
        return f"{n} blocks — build tower {names[0]} on top of {' on '.join(names[1:])}"
    if domain == "Ferry":
        n = params["cars"]
        steps = 4 * n - 1
        return f"{n} cars crossing left → right ({steps} sequential steps)"
    if domain == "Hanoi":
        n = params["discs"]
        steps = 2 ** n - 1
        return f"{n} discs, peg1 → peg3 ({steps} moves)"
    if domain == "Elevator":
        p, e, f = params["passengers"], params["elevators"], params["floors"]
        return f"{p} passenger{'s' if p>1 else ''}, {e} elevator{'s' if e>1 else ''}, {f} floors"
    return ""
