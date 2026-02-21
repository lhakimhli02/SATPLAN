# SATPLAN (Python)

Two SAT-based planning systems that convert PDDL problems into Boolean satisfiability problems.

- **`blackbox_python/`** — BlackBox: PDDL → GraphPlan → CNF → SAT. Python rewrite of the original BlackBox planner by Henry Kautz and Bart Selman.
- **`satplan_python/`** — SATplan: PDDL → STRIPS → CNF → SAT. Goes directly from grounded STRIPS actions to CNF, bypassing the planning graph.

---

## Requirements

- Python 3.10+
- PySAT: `pip install python-sat`
- Kissat (optional): `pip install passagemath-kissat`
- WalkSAT (optional): see [Building External Solvers](#building-external-solvers)

---

## BlackBox (`blackbox_python/`)

### Quick Start

```bash
cd SATPLAN/Blackbox/blackbox_python

# Run on the included example (Depot domain)
python blackbox.py -o pddl_problems/domain.pddl -f pddl_problems/problem.pddl
```

### Usage

```
python blackbox.py -o <domain.pddl> -f <problem.pddl> [options] [-solver <solver>]
```

**Important:** `-solver` must come last — it consumes all remaining arguments.

### Count Clauses (BlackBox)

Prints per-category CNF clause counts at each horizon, then solves and shows the plan:

```bash
python count_clauses.py -o pddl_problems/domain.pddl -f pddl_problems/problem.pddl
python count_clauses.py -o pddl_problems/domain.pddl -f pddl_problems/problem.pddl -maxtime 15
```

Output columns: `Vars`, `Total Clauses`, `Init`, `Goal`, `Precond`, `Frame`, `Mutex AMO`.

### Options (BlackBox)

| Flag | Description |
|------|-------------|
| `-o <file>` | Domain PDDL file |
| `-f <file>` | Problem PDDL file |
| `-g <file>` | Write plan to output file |
| `-t <int>` | Fixed plan length (0 = auto-increment, default) |
| `-i <level>` | Debug info level: 0 (quiet), 1 (verbose), 2 (detailed) |
| `-n` | Force negative facts |
| `-step <n>` | Graph increment step size (default: 1) |
| `-noskip` | Don't skip graphplan mutex checking |
| `-noopt` | Stop at first solution found |
| `-noincsat` | Disable incremental SAT across horizons |
| `-norelevance` | Disable action/schema relevance pruning |
| `-printlit` | Print WFF literals |
| `-printcnf` | Print DIMACS CNF encoding |
| `-axioms <n>` | SAT encoding preset (see below) |
| `-M <int>` | Max nodes per graph layer (default: 2048) |
| `-maxfail <n>` | Max solver failures before giving up (0 = unlimited) |
| `-maxauto <n>` | Max auto plan length (default: 100) |
| `-maxglobalsec <n>` | Global time limit in seconds |

### SAT Encoding Presets (`-axioms`, BlackBox only)

| Value | Name | Axioms Included |
|-------|------|-----------------|
| 7 | default | mutex actions + preconditions + frame axioms |
| 15 | -- | above + mutex facts |
| 31 | compressed | above + action implies effect (prunes some mutexes) |
| 63 | expanded | above + keeps all mutexes |
| 129 | action | mutex actions + action-to-action chaining (no fact propositions) |

### Project Structure (BlackBox)

```
blackbox_python/
  blackbox.py        Main entry point and argument parsing
  planner.py         Planning loop, solver dispatch, action minimization
  graphplan.py       Planning graph construction
  graph2wff.py       SAT encoding (CNF generation, AMO ladder encoding)
  sat_interface.py   SAT solver interfaces (PySAT, DPLL, Kissat, WalkSAT)
  utilities.py       Mutex computation (exists-step semantics)
  data_structures.py Core data types (Vertex, Operator, HashTable)
  pddl_parser.py     PDDL domain/problem parser
  justify.py         Plan justification (unnecessary action removal)
  count_clauses.py   Per-category clause counter + solver
  pddl_problems/     Example PDDL files
```

---

## SATplan (`satplan_python/`)

### Quick Start

```bash
cd SATPLAN/satplan_python

# Run on the included example (Depot domain)
python satplan.py -o pddl_problems/domain.pddl -f pddl_problems/problem.pddl
```

### Usage

```
python satplan.py -o <domain.pddl> -f <problem.pddl> [options] [-solver <solver>]
```

### Count Clauses (SATplan)

Prints per-category CNF clause counts at each horizon, then solves and shows the plan:

```bash
python count_clauses.py -o pddl_problems/domain.pddl -f pddl_problems/problem.pddl
python count_clauses.py -o pddl_problems/domain.pddl -f pddl_problems/problem.pddl -maxtime 15
python count_clauses.py -o pddl_problems/domain.pddl -f pddl_problems/problem.pddl -nomutex
```

Output columns: `Vars`, `New Clauses`, `Init (CWA)`, `Goal`, `Precond`, `Effects`, `Frame axioms`, `Mutex AMO`.

### Options (SATplan)

| Flag | Description |
|------|-------------|
| `-o <file>` | Domain PDDL file |
| `-f <file>` | Problem PDDL file |
| `-g <file>` | Write plan to output file |
| `-t <int>` | Fixed plan length (0 = auto-increment, default) |
| `-i <level>` | Debug info level: 0 (quiet), 1 (verbose), 2 (detailed) |
| `-n` | Force closed-world negation |
| `-step <n>` | Horizon increment step size (default: 1) |
| `-noopt` | Stop at first solution found |
| `-noincsat` | Disable incremental SAT across horizons |
| `-norelevance` | Disable action relevance pruning |
| `-noeffects` | Omit explicit effect clauses (rely on frame axioms only) |
| `-nomutex` | Disable mutex constraints |
| `-forallstep` | Use forall-step mutex semantics (default: exists-step) |
| `-nocwa` | Disable closed-world assumption at t=0 |
| `-printlit` | Print variable map |
| `-printcnf` | Print DIMACS CNF |
| `-maxfail <n>` | Max solver failures before giving up (0 = unlimited) |
| `-maxauto <n>` | Max auto horizon (default: 100) |
| `-maxglobalsec <n>` | Global time limit in seconds |

### Project Structure (SATplan)

```
satplan_python/
  satplan.py         Main entry point and argument parsing
  satplan_planner.py Planning loop, solver dispatch, action minimization
  grounder.py        PDDL grounding (STRIPS actions, type-based pruning)
  strips_encoder.py  Direct STRIPS-to-CNF encoding (frame axioms, AMO ladder)
  sat_interface.py   SAT solver interfaces (shared with blackbox_python)
  data_structures.py Core constants and types
  pddl_parser.py     PDDL domain/problem parser (shared with blackbox_python)
  count_clauses.py   Per-category clause counter + solver
  pddl_problems/     Example PDDL files
```

---

## Available Solvers (both versions)

| Solver | Backend | Incremental | Description |
|--------|---------|:-----------:|-------------|
| **cadical** | PySAT | Yes | CaDiCaL 1.9.5 — default, top SAT competition performer |
| **glucose** | PySAT | Yes | Glucose 4.2 — strong on industrial benchmarks |
| **maple** | PySAT | Yes | MapleChrono — SAT competition 2018 winner |
| **minisat** | PySAT | Yes | MiniSat — classic CDCL solver |
| **dpll** | Built-in Python | No | Pure DPLL with Jeroslow-Wang heuristic (no clause learning) |
| **kissat** | External binary | No | Kissat — state-of-the-art competition solver |
| **walksat** | External binary | No | WalkSAT — stochastic local search (incomplete) |
| **graphplan** | Built-in | — | Backward-chaining search, BlackBox only |

**Notes:**
- *Incremental* solvers reuse learned clauses across plan horizons. Non-incremental solvers rebuild from scratch at each horizon and are significantly slower on large problems.
- *WalkSAT* is **incomplete**: it can find satisfying assignments but cannot prove unsatisfiability. It returns timeout (not UNSAT) when it fails.

## Running with a Specific Solver

```bash
# Default (CaDiCaL)
python blackbox.py -o domain.pddl -f problem.pddl
python satplan.py  -o domain.pddl -f problem.pddl

# Glucose
python blackbox.py -o domain.pddl -f problem.pddl -solver glucose

# WalkSAT with 10-second timeout per horizon
python blackbox.py -o domain.pddl -f problem.pddl -solver -maxsec 10 walksat
```

## Solver Chaining

Chain solvers with timeouts using `-then`. If the first solver times out, the next takes over.

```bash
# Try Glucose for 30 seconds, then fall back to CaDiCaL
python blackbox.py -o domain.pddl -f problem.pddl -solver -maxsec 30 glucose -then cadical

# Three-stage chain
python blackbox.py -o domain.pddl -f problem.pddl -solver -maxsec 10 maple -then -maxsec 60 glucose -then cadical
```

## Action Minimization

After finding a plan at the minimum makespan, both planners search for plans with fewer total actions at longer makespans using PySAT cardinality constraints (sequential counter encoding). Use `-noopt` to skip this and return the first plan found.

---

## How the Two Planners Differ

| | BlackBox | SATplan |
|--|---------|---------|
| **Pipeline** | PDDL → GraphPlan graph → CNF | PDDL → ground STRIPS → CNF |
| **Grounding** | Layered planning graph | Direct enumeration with static-predicate type pruning |
| **Mutex source** | Graph-level mutex propagation | Exists-step sequential applicability check |
| **Frame axioms** | Fact-level (graph layer) | Explanatory frame axioms per fluent per step |
| **Effect clauses** | Optional (`-axioms 31+`) | Always emitted (or disabled with `-noeffects`) |
| **Unique options** | `-axioms`, `-noskip`, `-M`, `graphplan` solver | `-nocwa`, `-noeffects`, `-nomutex`, `-forallstep` |

---

## SAT Encoding (both planners)

- **AMO ladder encoding**: Mutex cliques use ladder at-most-one (3(k−1) clauses) instead of pairwise (k(k−1)/2).
- **Exists-step semantics**: Two actions are mutex only if both sequential orderings fail (fewer constraints than forall-step).
- **Incremental encoding**: Only newly-added time layers are encoded per horizon, reusing learned clauses across horizons.

---

## Supported PDDL

Typed STRIPS only:
- `:strips`
- `:typing`
- `:equality`

Does **not** support: conditional effects, disjunctive preconditions, quantified goals, derived predicates, numeric fluents, or durative actions.

---

## Building External Solvers

### Kissat

```bash
pip install passagemath-kissat
```

Or build from source:

```bash
git clone https://github.com/arminbiere/kissat.git
cd kissat
./configure && make
cp build/kissat /usr/local/bin/
```

### WalkSAT

```bash
git clone https://gitlab.com/HenryKautz/Walksat.git
cd Walksat/Walksat_v56
make
```

Place the `walksat` binary on your PATH or in the same directory as `blackbox.py` / `satplan.py`.
