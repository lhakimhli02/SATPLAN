# SATPLAN Project — Progress Report

**Date:** April 23, 2026  
**Repository:** `lhakimhli02/SATPLAN` (`/Users/lukashakim/SATPLAN/`)

---

## Overview

This project implements two complete SAT-based AI planning systems entirely in Python, along with graph visualizers, animated plan demonstrations, and a full suite of analysis utilities. Both systems read standard PDDL domain and problem files and produce plans by encoding the planning problem as a Boolean satisfiability (SAT) instance and calling modern SAT solvers.

The two planners take different routes to the same goal:

| System | Route |
|--------|-------|
| **BlackBox** (`blackbox_python/`) | PDDL → GraphPlan graph → CNF → SAT |
| **SATplan** (`satplan_python/`) | PDDL → ground STRIPS actions → CNF → SAT |

---

## 1. BlackBox Python (`blackbox_python/`)

A complete Python rewrite of the classic BlackBox planner (Kautz & Selman, 1998).

### Pipeline

```
PDDL files
    │
    ▼
pddl_parser.py      ← typed STRIPS parser
    │
    ▼
graphplan.py         ← layered planning graph (fact + action layers, mutex propagation)
    │
    ▼
graph2wff.py         ← CNF encoding (axiom presets, AMO ladder, incremental)
    │
    ▼
sat_interface.py     ← SAT solver dispatch (PySAT / Kissat / WalkSAT / DPLL)
    │
    ▼
planner.py           ← search loop, solver chaining, action minimization
    │
    ▼
justify.py           ← unnecessary action removal from solution
```

### Module Details

| File | Role |
|------|------|
| `blackbox.py` | CLI entry point; argument parsing, solver spec parsing, timing breakdown |
| `planner.py` | Planning loop; iterative horizon search; solver dispatch; action minimization via PySAT cardinality constraints; plan output |
| `graphplan.py` | `PlanningGraph` class; layered fact/action tables; mutex propagation; relevance pruning; incremental graph extension |
| `graph2wff.py` | `SATEncoder` class; CNF generation for five axiom types; AMO ladder encoding; incremental skip optimization; DIMACS output |
| `sat_interface.py` | Solver wrappers for CaDiCaL, Glucose, Maple, MiniSat (PySAT), Kissat (external binary), WalkSAT (stochastic), DPLL (pure Python); `IncrementalSATSolver` session class |
| `utilities.py` | Mutex computation (exists-step semantics); fact/action mutex helpers |
| `data_structures.py` | Core types: `Vertex`, `Operator`, `HashTable`, `SolverSpec`, result codes |
| `pddl_parser.py` | Typed STRIPS PDDL parser (`:strips`, `:typing`, `:equality`) |
| `justify.py` | Backward-chaining plan justification to remove redundant actions |
| `count_clauses.py` | Per-category clause counter; reports `Vars / Total / Init / Goal / Precond / Frame / Mutex AMO` at each horizon |

### SAT Encoding Presets (`-axioms`)

| Value | Axioms included |
|-------|----------------|
| 7 (default) | Mutex actions + preconditions + frame axioms |
| 15 | Above + mutex facts |
| 31 | Above + action implies effect (compressed) |
| 63 | Above + redundant clauses (expanded) |
| 129 | Mutex actions + action-to-action chaining only (no fact propositions) |

### Key Engineering Choices

- **AMO ladder encoding**: mutex cliques of size ≥ 4 use the ladder at-most-one scheme — O(3(k−1)) clauses versus O(k(k−1)/2) for pairwise. Smaller cliques (≤ 3) use pairwise for simplicity.
- **Exists-step semantics**: two actions are mutex only if *both* sequential orderings fail their preconditions — strictly less constrained than forall-step, enabling more parallel plans.
- **Incremental SAT**: learned clauses are reused across horizons; only newly added graph layers are encoded per iteration.
- **Solver chaining**: `-solver -maxsec 30 glucose -then cadical` tries Glucose with a 30s timeout, then falls back to CaDiCaL if it times out.
- **Action minimization**: after finding a plan at the minimum makespan, the planner searches longer makespans for plans with fewer total actions using PySAT sequential counter cardinality constraints.

### PDDL Benchmarks Included

| Problem | Domain |
|---------|--------|
| `blocksworld_problem.pddl` | 3-block Blocksworld |
| `elevator_problem.pddl` | 4 floors, 2 passengers, 1 elevator |
| `elevator_problem2.pddl` | 6 floors, 3 passengers, 2 elevators |

Additional benchmark suites under `Blackbox/BlackBox-master/Examples/`: Logistics (STRIPS and typed, 30 problems), Bulldozer, Fridge, Tire-World, Woodshop, Move-BW (large), Prodigy-BW (large).

---

## 2. SATplan Python (`satplan_python/`)

An original direct STRIPS-to-SAT planner that bypasses the planning graph entirely.

### Pipeline

```
PDDL files
    │
    ▼
pddl_parser.py       ← shared parser
    │
    ▼
grounder.py          ← STRIPSProblem + GroundAction; type-based pruning
    │
    ▼
strips_encoder.py    ← STRIPSEncoder; explanatory frame axioms, AMO ladder, incremental
    │
    ▼
sat_interface.py     ← shared SAT solver layer
    │
    ▼
satplan_planner.py   ← planning loop, solver dispatch, action minimization
```

### Module Details

| File | Role |
|------|------|
| `satplan.py` | CLI entry point; same flags as `blackbox.py` plus STRIPS-specific flags |
| `satplan_planner.py` | Planning loop identical in structure to `planner.py`; action minimization; plan output |
| `grounder.py` | `STRIPSProblem` + `GroundAction`; enumerates all type-compatible object combinations per action schema; static-predicate type pruning |
| `strips_encoder.py` | `STRIPSEncoder`; fluent and action variables; initial state (CWA); precondition, effect, and explanatory frame axiom clauses; exists-step mutex; AMO ladder; incremental encoding |
| `count_clauses.py` | Per-category clause counter: `Vars / New Clauses / Init (CWA) / Goal / Precond / Effects / Frame axioms / Mutex AMO` |

### Encoding (per time step `t`)

1. **Initial state (CWA):** `[+f₀]` for all `f ∈ init`; `[-f₀]` for all `f ∉ init`.
2. **Goal state:** `[+f_T]` or `[-f_T]` for each goal literal (encoded as SAT assumptions for incremental solving).
3. **Preconditions:** `¬aₜ ∨ fₜ` (positive) and `¬aₜ ∨ ¬fₜ` (negative).
4. **Effects:** `¬aₜ ∨ f_{t+1}` (add) and `¬aₜ ∨ ¬f_{t+1}` (delete).
5. **Explanatory frame axioms:**
   - Becomes-true: `[¬f_{t+1}, fₜ, adder₁_t, …]`
   - Becomes-false: `[f_{t+1}, ¬fₜ, deleter₁_t, …]`
6. **Mutex:** `¬a1_t ∨ ¬a2_t` for action pairs whose both sequential orderings violate preconditions (exists-step only).

### Bugs Found and Fixed

**Bug 1 — Type-based grounding pruning (grounder.py)**

The original `_infer_param_types_from_preconds` method used *any* unary initial-state predicate as a type constraint — including changing fluents like `clear`. For example, `clear` was true initially for blocks `a` and `c` but not `b`, so the action `stack_a_b` was pruned because `clear(b)` was false at `t=0`. Goal fluents like `on(a,b)` ended up with no adder actions, making the problem permanently UNSAT.

**Fix:** Added `_collect_effect_predicates(ops)` to identify all predicates that appear in any action's effects. `_infer_param_types_from_preconds` now skips any predicate that appears in effects, using only truly static predicates (e.g., `truck`, `depot`, `driver`) as type filters.

**Bug 2 — Exists-step mutex computation (strips_encoder.py)**

The initial mutex check incorrectly included "inconsistent effects" (`a.del_eff & b.add_eff` and vice versa) as a reason to declare two actions non-parallel. These conflicts do not prevent sequential ordering from succeeding. Only precondition violations (`a.del_eff & b.pos_pre` and `a.add_eff & b.neg_pre`) matter.

**Fix:** Removed the inconsistent-effects checks from the exists-step mutex predicate; now only precondition interference is tested.

### Benchmark Results

| Problem | Optimal horizon | Actions in plan | Solve time |
|---------|:--------------:|:--------------:|:-----------:|
| Blocksworld 3 blocks (`on_a_b ∧ on_b_c`) | 6 | 6 | ~0.01 s |
| Depot (`depotprob1818`) | 4 | 15 | ~0.08 s |
| Trivial 1-action problem | 1 | 1 | <0.01 s |

### Additional Flags (SATplan only)

| Flag | Effect |
|------|--------|
| `-nocwa` | Disable closed-world assumption at t=0 |
| `-noeffects` | Omit explicit effect clauses (rely on frame axioms alone) |
| `-nomutex` | Disable all mutex constraints |
| `-forallstep` | Use forall-step mutex (more constrained than exists-step) |
| `-sequential` | At most one action per time step |

---

## 3. Graph Visualization (`visualize_graphplan.py`, `visualize_graphplan_clustered.py`)

Interactive/static renderers for the BlackBox planning graph, built with `matplotlib`.

### Standard Renderer (`visualize_graphplan.py`)

Three-column layout per layer: **Facts @ t | Actions @ t | Facts @ t+1**.


### Clustered Renderer (`visualize_graphplan_clustered.py`)

Alternative predicate-clustered layout for Blocksworld. Groups facts by predicate in a semantic status-board layout:
- Top ~55%: `on(x,y)` N×N reachability grid
- Middle strips: `clear(x)`, `ontable(x)`, `holding(x)`, `handempty`
- Bottom ~20%: real actions in compact multi-column list
- No edge drawing — focuses on fact reachability state

---

## 4. Animations (`animate_blocksworld.py`, `animate_elevator.py`)

### Demos

**Blocksworld**

<video src="BlocksWorld_Demo.mp4" controls width="100%"></video>

**Elevator**

<video src="Elevator_demo.mp4" controls width="100%"></video>



Two-panel `matplotlib` animations combining the planning graph with a world-state visualization. Both support `--save <path>` to export MP4 or GIF.

### Blocksworld Animation (`animate_blocksworld.py`)

- **Left panel:** Planning graph growing horizon by horizon.
- **Right panel:** Robotic-arm blocks world. Block movement uses smooth three-phase interpolation (lift → slide → lower).
- **Search phase:** shows the best partial plan found so far (highest number of goals achieved) with its final state.
- **Execution phase:** once a plan is found, animates it step by step.
- Goal blocks are highlighted with a green border.
- `--clustered` flag switches the left panel to the predicate-clustered layout.

### Elevator Animation (`animate_elevator.py`)

- **Left panel:** Same planning-graph renderer.
- **Right panel:** Building schematic with elevator shaft(s), a smoothly moving car, and passengers as colored circles. Passengers inside the car appear as smaller inset circles.
- Supports multi-elevator problems (`elevator_problem2.pddl`).
- Goal passengers highlighted with a green border.
- 12 sub-frames per execution step at 20 fps.

### Shared Animation Options

| Flag | Description |
|------|-------------|
| `--steps N` | Max horizons to search |
| `--interval N` | Milliseconds per logical plan step |
| `--save <path>` | Export as `.mp4` or `.gif` |
| `--no-noop` | Hide NOOP actions in graph panel |
| `--max-facts N` | Cap fact nodes displayed per column |
| `--max-actions N` | Cap action nodes displayed per column |

---

## 5. SAT Solvers Available (Both Planners)

| Solver | Backend | Incremental | Notes |
|--------|---------|:-----------:|-------|
| `cadical` | PySAT (CaDiCaL 1.9.5) | Yes | Default; top SAT competition performer |
| `glucose` | PySAT (Glucose 4.2) | Yes | Strong on industrial benchmarks |
| `maple` | PySAT (MapleChrono) | Yes | SAT Competition 2018 winner |
| `minisat` | PySAT (MinisatGH) | Yes | Classic CDCL solver |
| `dpll` | Pure Python | No | Jeroslow-Wang heuristic; no clause learning |
| `kissat` | External binary | No | State-of-the-art; pip or build from source |
| `walksat` | External binary | No | Stochastic local search; incomplete (no UNSAT proof) |
| `graphplan` | Built-in | — | BlackBox only; backward-chaining search |

Incremental solvers reuse learned clauses across horizons — significantly faster on large problems.

---

## 6. SATplan AIMA (`SATplan_AIMA/`)

An earlier prototype implementing `SATPlan` through the AIMA (Russell & Norvig) planning framework. Uses propositional logic encoding with a CDCL solver (`cdcl_satisfiable`) from `logic.py`. Includes:

- `planning.py` — `PlanningProblem`, `Action`, `SATPlan`
- `logic.py` — propositional logic, `to_cnf`, `cdcl_satisfiable`
- `run_blocks_satplan.py` — Blocksworld demo (iterates horizons 0–10)
- `driver_log_satplan.py` — DriverLog domain demo

This module served as the baseline before the full PDDL-based rewrite.

---

## 7. IPC Benchmark Domains

The `IPC3/` directory contains International Planning Competition 3 domains for future benchmarking:

- **Depots** (Strips, Numeric, SimpleTime, Time)
- **DriverLog** (Strips, Numeric, SimpleTime, Time, HardNumeric)
- **ZenoTravel** (Strips, Numeric, SimpleTime, Time)
- **Rovers** (Strips, Numeric, SimpleTime, Time)
- **Satellite** (Strips, Numeric, SimpleTime, Time, Complex, HardNumeric)
- **FreeCell**, **Settlers**

The Strips variants are compatible with both planners.

---

## 8. Supported PDDL Subset

Both planners support typed STRIPS:

| Supported | Not supported |
|-----------|--------------|
| `:strips` | Conditional effects |
| `:typing` | Disjunctive preconditions |
| `:equality` | Quantified goals |
| — | Derived predicates |
| — | Numeric fluents |
| — | Durative actions |

---

## Summary of Key Achievements

1. **Full Python rewrite of BlackBox** — complete PDDL → GraphPlan → CNF → SAT pipeline with 8 solver backends, solver chaining, incremental encoding, and action minimization.
2. **Original direct STRIPS-to-SAT planner** — independent implementation without a planning graph intermediate; faster on some benchmarks (Depot: 15 actions at horizon 4 in 0.08 s).
3. **Two critical bugs diagnosed and fixed** in the STRIPS grounding and mutex computation, enabling correct solutions on standard benchmarks.
4. **Interactive planning graph visualizer** with two layout modes (standard and predicate-clustered).
5. **Two animated demos** (Blocksworld and Elevator) combining live graph growth with smooth world-state simulation, exportable as MP4/GIF.
6. **Shared infrastructure** — `pddl_parser.py`, `sat_interface.py`, `data_structures.py` are reused across both planners with no duplication.
7. **Clause analysis utility** (`count_clauses.py`) for profiling CNF encoding size by category at each horizon.
