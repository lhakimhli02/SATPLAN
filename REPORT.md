# SATPLAN Project — Progress Report

**Date:** April 23, 2026  
**Repository:** `lhakimhli02/SATPLAN`

---

## Overview

This project builds two complete **AI planning systems** in Python. Given a description of a world (what actions are possible, what the starting state is, and what goal you want to reach), both systems automatically find a sequence of actions — a **plan** — that gets from the start to the goal.

The core idea is to turn the planning problem into a **Boolean satisfiability (SAT)** problem: encode everything as logical clauses and ask a SAT solver whether a plan of length *T* exists. If the solver says "satisfiable", it returns a model that directly decodes into a plan.

Both systems use **PDDL** (Planning Domain Definition Language), the standard file format used in AI planning research and competitions to describe actions and problems.

### What is GraphPlan?

GraphPlan is a classic planning algorithm (Blum & Furst, 1997). It builds a **planning graph** — a layered data structure that alternates between *fact layers* (what is true at step *t*) and *action layers* (what actions can fire at step *t*). It also tracks **mutexes** — pairs of facts or actions that cannot both be true/applied at the same time step. This graph compactly encodes all possible parallelizable plans up to a given horizon.

### What is SATPlan / BlackBox?

**SATPlan** (Kautz & Selman, 1992) encodes the planning problem as a SAT formula and hands it to a modern SAT solver. **BlackBox** (Kautz & Selman, 1998) combines both ideas: first build a GraphPlan graph to get structure and mutex information, then encode *that graph* as CNF clauses and solve with SAT. This is often faster than pure GraphPlan backward search because modern SAT solvers are highly optimized.

### The Two Planners at a Glance

| System | Approach |
|--------|----------|
| **BlackBox** (`blackbox_python/`) | PDDL → GraphPlan graph → CNF → SAT solver |
| **SATplan** (`satplan_python/`) | PDDL → ground STRIPS actions → CNF → SAT solver |

The key difference: BlackBox builds a planning graph first and encodes that; SATplan skips the graph entirely and encodes the grounded actions directly.

---

## 1. BlackBox Python (`blackbox_python/`)

A complete Python rewrite of the classic BlackBox planner (Kautz & Selman, 1998).

### How It Works (Step by Step)

1. **Parse PDDL** — read the domain (action schemas) and problem (objects, initial state, goal).
2. **Build a planning graph** — starting from the initial facts, repeatedly apply all applicable actions to grow a layered graph of reachable facts and actions. Track mutex pairs at each layer (facts or actions that can never both hold at the same step).
3. **Encode as CNF** — convert the graph into a set of logical clauses (the SAT formula). Each fact and action at each time step becomes a Boolean variable. Clauses enforce preconditions, effects, frame axioms (things stay true unless changed), and mutex constraints.
4. **Call a SAT solver** — if the solver finds a satisfying assignment, decode it back into a plan. If not, extend the graph by one step and try again.
5. **Minimize actions** — once a plan is found, search for shorter plans (fewer total actions) at slightly longer makespans.

### Pipeline

```
PDDL files
    │
    ▼
pddl_parser.py      ← reads domain and problem files
    │
    ▼
graphplan.py        ← builds the layered planning graph + mutex sets
    │
    ▼
graph2wff.py        ← encodes the graph as CNF clauses
    │
    ▼
sat_interface.py    ← calls the SAT solver
    │
    ▼
planner.py          ← search loop, solver chaining, action minimization
    │
    ▼
justify.py          ← removes unnecessary actions from the solution
```

### Module Details

| File | Role |
|------|------|
| `blackbox.py` | CLI entry point; argument parsing, solver spec parsing, timing breakdown |
| `planner.py` | Planning loop; iterative horizon search; solver dispatch; action minimization via cardinality constraints; plan output |
| `graphplan.py` | Builds the layered planning graph; tracks reachable facts and actions at each step; computes mutex pairs; supports incremental extension |
| `graph2wff.py` | Converts the planning graph to CNF clauses; supports five axiom encoding presets; uses AMO ladder encoding for mutex cliques |
| `sat_interface.py` | Wrappers for 7 SAT solver backends; stateful incremental solver session that reuses learned clauses across horizons |
| `utilities.py` | Mutex computation helpers (exists-step semantics) |
| `data_structures.py` | Core types: `Vertex`, `Operator`, `HashTable`, `SolverSpec`, result codes |
| `pddl_parser.py` | Typed STRIPS PDDL parser (`:strips`, `:typing`, `:equality`) |
| `justify.py` | Removes redundant actions from the found plan |
| `count_clauses.py` | Prints per-category clause counts (`Vars / Total / Init / Goal / Precond / Frame / Mutex AMO`) at each horizon |

### SAT Encoding Presets (`-axioms`)

These control which logical constraints are included in the CNF formula. More constraints can prune the search space but add more clauses.

| Value | What's included |
|-------|----------------|
| 7 (default) | Mutex actions + preconditions + frame axioms |
| 15 | Above + mutex facts |
| 31 | Above + explicit action → effect clauses |
| 63 | Above + redundant (but sometimes helpful) clauses |
| 129 | Action-only encoding (no explicit fact propositions) |

### Key Engineering Choices

- **AMO ladder encoding**: when many actions are mutually exclusive, encoding "at most one fires" with a ladder structure uses O(3k) clauses instead of O(k²) for pairwise — much more efficient for large mutex cliques.
- **Exists-step semantics**: two actions are only declared mutex if *both* orderings (A then B, and B then A) violate a precondition. This is less restrictive than forall-step, allowing more parallelism in plans.
- **Incremental SAT**: instead of re-solving from scratch at each horizon, the solver session is kept alive and only new clauses are added. The solver can reuse everything it already learned.
- **Solver chaining**: try one solver with a time limit, automatically fall back to another if it times out (e.g., `-solver -maxsec 30 glucose -then cadical`).

### PDDL Benchmarks Included

| Problem | Description |
|---------|-------------|
| `blocksworld_problem.pddl` | Stack 4 blocks into a tower |
| `elevator_problem.pddl` | 4 floors, 2 passengers, 1 elevator |
| `elevator_problem2.pddl` | 6 floors, 3 passengers, 2 elevators |

Additional benchmark suites under `Blackbox/BlackBox-master/Examples/`: Logistics (30 problems, STRIPS and typed), Bulldozer, Fridge, Tire-World, Woodshop, and large Blocksworld variants.

---

## 2. SATplan Python (`satplan_python/`)

An original direct STRIPS-to-SAT planner that skips the planning graph entirely.

### How It Differs from BlackBox

Instead of building a planning graph first, SATplan **grounds** the PDDL actions directly — substituting all possible object combinations into each action schema to produce a flat list of concrete actions (e.g., `stack_A_B`, `stack_A_C`, `unstack_B_C`, …). It then encodes these grounded actions directly into CNF clauses without any intermediate graph structure.

This is simpler conceptually and avoids the graph construction cost, but loses the mutex propagation information that GraphPlan provides for free.

### Pipeline

```
PDDL files
    │
    ▼
pddl_parser.py       ← shared parser (same as BlackBox)
    │
    ▼
grounder.py          ← instantiates all concrete actions from schemas
    │
    ▼
strips_encoder.py    ← encodes actions + fluents directly as CNF
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
| `satplan.py` | CLI entry point; same flags as `blackbox.py` plus a few STRIPS-specific extras |
| `satplan_planner.py` | Planning loop; action minimization; plan output |
| `grounder.py` | Instantiates all type-compatible ground actions from PDDL schemas; prunes using static predicates |
| `strips_encoder.py` | Encodes fluent/action variables, initial state, goal, preconditions, effects, frame axioms, and mutex clauses into CNF |
| `count_clauses.py` | Per-category clause counter: `Vars / New Clauses / Init (CWA) / Goal / Precond / Effects / Frame axioms / Mutex AMO` |

### CNF Encoding Explained

For each time step `t`, the following clauses are added:

| Clause type | What it says | Formula |
|------------|-------------|---------|
| **Initial state** | Every fluent is explicitly set true or false at t=0 (closed-world assumption) | `[+f₀]` or `[-f₀]` |
| **Goal** | Required fluents must hold at the final step T | `[+f_T]` or `[-f_T]` |
| **Preconditions** | If an action fires, its required facts must hold | `¬aₜ ∨ fₜ` |
| **Effects** | If an action fires, it changes the world | `¬aₜ ∨ f_{t+1}` |
| **Frame axioms** | Facts only change if some action caused the change | `¬f_{t+1} ∨ fₜ ∨ (adders…)` |
| **Mutex** | Conflicting actions can't both fire at step t | `¬a1_t ∨ ¬a2_t` |

### Bugs Found and Fixed

**Bug 1 — Incorrect type-based grounding pruning**

The grounder tried to be smart: it looked at unary predicates in a precondition (like `clear(x)`) to infer what type `x` should be, and then only grounded actions for objects where that predicate was true in the initial state.

The problem: `clear` is a *changing* fluent — it starts true for some blocks but becomes false when you stack something on them. Using it as a type filter meant actions like `stack_A_B` were pruned because `clear(B)` happened to be false in the initial state. This made the goal `on(A, B)` unreachable (no action could add it), so the problem was always UNSAT.

**Fix:** Only use *static* predicates — ones that never appear in any action's effects — as type filters. Dynamic predicates like `clear` are now ignored during pruning.

**Bug 2 — Wrong mutex condition**

The initial mutex check declared two actions incompatible if their effects conflicted (e.g., one adds `f` and the other deletes `f`). But conflicting effects don't actually prevent the actions from being applied in sequence — they just mean one undoes the other. Only *precondition* violations matter for exists-step mutex.

**Fix:** Removed the effect-conflict check; only precondition interference (`a.del_eff ∩ b.pos_pre ≠ ∅` or vice versa) triggers a mutex.

### Benchmark Results

| Problem | Horizon found | Actions | Solve time |
|---------|:------------:|:-------:|:----------:|
| Blocksworld 4 blocks | 6 | 6 | ~0.01 s |
| Depot (`depotprob1818`) | 4 | 15 | ~0.08 s |
| Trivial 1-action problem | 1 | 1 | <0.01 s |

### SATplan-Only Flags

| Flag | Effect |
|------|--------|
| `-nocwa` | Disable closed-world assumption at t=0 (unknown fluents left unset) |
| `-noeffects` | Omit explicit effect clauses (rely on frame axioms only) |
| `-nomutex` | Disable all mutex constraints |
| `-forallstep` | Stricter mutex: actions are mutex if either ordering fails (fewer parallel actions allowed) |
| `-sequential` | Allow at most one action per time step (sequential planning) |

---

## 3. Graph Visualization

Two interactive graph renderers built with `matplotlib` let you see the planning graph grow layer by layer.

### Standard Renderer (`visualize_graphplan.py`)

Displays three columns per layer: **Facts @ t | Actions @ t | Facts @ t+1**.

**Color key:**
- Blue = reachable fact
- Yellow = goal fact  
- Green = real action
- Gray = no-op (a "do nothing" placeholder action)
- Red border = has at least one mutex partner

**Edge key:**
- Dark edges = precondition links (fact required by action)
- Green edges = positive effect (action adds this fact)
- Red edges = delete effect (action removes this fact)
- Red arcs = mutex pair

**Navigation:** Left/Right arrow keys step through layers; `s` saves the current layer as PNG; `q` or Escape quits.

### Clustered Renderer (`visualize_graphplan_clustered.py`)

An alternative layout designed for Blocksworld. Instead of edges, it groups facts by predicate into a semantic status board:
- Top: `on(x,y)` shown as an N×N reachability grid
- Middle: `clear(x)`, `ontable(x)`, `holding(x)`, `handempty`
- Bottom: real actions in a compact list

This makes it easier to see *what is true* at each horizon rather than tracing individual causal links.

---

## 4. Animations

Two animated demos show the planner working in real time. Each uses a two-panel layout: the **planning graph growing** on the left and the **world executing the plan** on the right.

### Demos

**Blocksworld** — a robotic arm stacks blocks into a goal configuration

![Blocksworld demo](BlocksWorld_Demo.gif)

**Elevator** — one or two elevators deliver passengers to their goal floors

![Elevator demo](Elevator_demo.gif)

### What the Animation Shows

1. **Search phase** (before a plan is found): the planning graph grows one layer per frame. The world panel shows the best partial plan found so far — how close the planner is getting to the goal.
2. **Execution phase** (once a plan is found): the world panel animates the plan step by step with smooth interpolation.

### Blocksworld (`animate_blocksworld.py`)

- Block movement uses three-phase smooth interpolation: lift → slide → lower.
- Goal blocks are highlighted with a green border.
- `--clustered` flag switches the graph panel to the predicate-clustered layout.

### Elevator (`animate_elevator.py`)

- Building schematic with shaft(s), a smoothly moving car, and passengers as colored circles.
- Passengers inside the car appear as smaller inset circles.
- Supports single and multi-elevator problems.

### Animation Options (both scripts)

| Flag | Description |
|------|-------------|
| `--steps N` | Max horizons to search before giving up |
| `--interval N` | Milliseconds per plan step during execution |
| `--save <path>` | Export as `.mp4` or `.gif` instead of displaying |
| `--no-noop` | Hide no-op actions in the graph panel |
| `--max-facts N` | Cap the number of fact nodes shown per column |
| `--max-actions N` | Cap the number of action nodes shown per column |

---

## 5. Available SAT Solvers

Both planners support the same set of SAT solver backends. Modern CDCL solvers (CaDiCaL, Glucose, etc.) are dramatically faster than naive search for most planning problems.

| Solver | How it's used | Incremental? | Notes |
|--------|--------------|:------------:|-------|
| `cadical` | PySAT library | Yes | Default; top-ranked in SAT competitions |
| `glucose` | PySAT library | Yes | Strong on structured/industrial problems |
| `maple` | PySAT library | Yes | SAT Competition 2018 winner |
| `minisat` | PySAT library | Yes | Classic baseline CDCL solver |
| `dpll` | Pure Python | No | Basic DPLL with Jeroslow-Wang heuristic; educational |
| `kissat` | External binary | No | State-of-the-art; install via pip or build from source |
| `walksat` | External binary | No | Stochastic local search; fast but can't prove UNSAT |
| `graphplan` | Built-in | — | BlackBox only; classic backward-chaining search (no SAT) |

**Incremental** means the solver session stays open across horizons — learned clauses carry over, so the solver doesn't start from scratch every time the horizon grows. This makes a large difference in speed on harder problems.

---

## 6. SATplan AIMA (`SATplan_AIMA/`)

An earlier prototype that implements SATPlan using the code framework from the textbook *Artificial Intelligence: A Modern Approach* (Russell & Norvig). This was the starting point before the full PDDL-based rewrite.

It encodes planning problems as propositional logic formulas and solves them with a built-in CDCL solver. Included demos:
- `run_blocks_satplan.py` — Blocksworld (tries horizons 0–10)
- `driver_log_satplan.py` — DriverLog domain

This module is useful as a simpler, more readable reference for understanding how SATPlan works at a high level before diving into the full PDDL systems.

---

## 7. IPC Benchmark Domains (`IPC3/`)

This directory contains planning domains from the **International Planning Competition 3** — a major benchmark suite used to evaluate AI planners. Each domain comes in several variants (STRIPS-only, Numeric, Timed, etc.). The STRIPS variants work directly with both planners.

| Domain | What it models |
|--------|---------------|
| Depots | Moving crates between depots using trucks and hoists |
| DriverLog | Routing trucks and drivers across a road network |
| ZenoTravel | Flying passengers between cities (fuel-aware) |
| Rovers | Planetary rovers collecting samples and transmitting data |
| Satellite | Scheduling satellite instruments to take images |
| FreeCell | The card game |
| Settlers | Resource-gathering and settlement building |

---

## 8. Supported PDDL

Both planners handle **typed STRIPS** — the most common planning problem format. More advanced PDDL features (numeric quantities, time, conditional effects) are not supported.

| Supported | Not supported |
|-----------|--------------|
| `:strips` — basic add/delete effects | Conditional effects |
| `:typing` — typed objects | Disjunctive preconditions |
| `:equality` — object equality tests | Quantified goals (`forall`, `exists`) |
| | Derived predicates |
| | Numeric fluents |
| | Durative (timed) actions |

---

## Summary

| What was built | Details |
|---------------|---------|
| BlackBox planner (Python rewrite) | PDDL → GraphPlan → CNF → SAT; 8 solver backends; incremental encoding; action minimization |
| SATplan (original) | Direct STRIPS → CNF without a planning graph; faster on some benchmarks |
| Two critical bugs fixed | Grounding pruning (static vs. dynamic predicates) and mutex computation |
| Planning graph visualizer | Two layout modes: standard edge-based and predicate-clustered |
| Animated demos | Blocksworld and Elevator with live graph growth + smooth world execution |
| Shared infrastructure | Parser, SAT interface, and data structures reused across both planners |
| Clause analysis tool | Per-category CNF clause counter for profiling encoding size |
