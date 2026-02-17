# BlackBox SATPLAN (Python)

A SAT-based planning system that converts PDDL problems into Boolean satisfiability problems. This is a Python rewrite of the original BlackBox planner by Henry Kautz and Bart Selman.

## Requirements

- Python 3.10+
- PySAT: `pip install python-sat`

## Basic Usage

```
python blackbox.py -o <domain.pddl> -f <problem.pddl>
```

### Required Arguments

| Flag | Description |
|------|-------------|
| `-o <file>` | Domain PDDL file |
| `-f <file>` | Problem PDDL file |

## Available Solvers

All SAT solvers are provided via the [PySAT](https://pysathq.github.io/) library.

| Solver | Aliases | Description |
|--------|---------|-------------|
| **cadical** | `cadical`, `cd195` | CaDiCaL 1.9.5 — default solver, top SAT competition performer |
| **glucose** | `glucose`, `g42` | Glucose 4.2 — strong on industrial benchmarks |
| **maple** | `maple`, `mcb` | MapleChrono — SAT competition 2018 winner |
| **graphplan** | `graphplan` | Built-in backward-chaining search (not SAT-based) |

## Running with a Specific Solver

### Use the default solver (CaDiCaL)

```
python blackbox.py -o domain.pddl -f problem.pddl
```

### Use Glucose

```
python blackbox.py -o domain.pddl -f problem.pddl -solver glucose
```

### Use MapleChrono

```
python blackbox.py -o domain.pddl -f problem.pddl -solver maple
```

### Use GraphPlan (no SAT)

```
python blackbox.py -o domain.pddl -f problem.pddl -solver graphplan
```

## Solver Chaining

You can chain solvers with timeouts using `-then`. If the first solver times out, the next one takes over.

### Try Glucose for 30 seconds, then fall back to CaDiCaL

```
python blackbox.py -o domain.pddl -f problem.pddl -solver -maxsec 30 glucose -then cadical
```

### Try GraphPlan first, then CaDiCaL

```
python blackbox.py -o domain.pddl -f problem.pddl -solver graphplan -then cadical
```

### Three-stage chain

```
python blackbox.py -o domain.pddl -f problem.pddl -solver -maxsec 10 maple -then -maxsec 60 glucose -then cadical
```

## Other Options

| Flag | Description |
|------|-------------|
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

## SAT Encoding Presets (`-axioms`)

| Value | Name | Axioms Included |
|-------|------|-----------------|
| 7 | default | mutex actions + preconditions + frame axioms |
| 15 | — | above + mutex facts |
| 31 | compressed | above + action implies effect (prunes some mutexes) |
| 63 | expanded | above + keeps all mutexes |
| 129 | action | mutex actions + action-to-action chaining (no fact propositions) |

## Supported PDDL

Typed STRIPS only:

- `:strips`
- `:typing`
- `:equality`

Does **not** support: conditional effects, disjunctive preconditions, quantified goals, derived predicates, numeric fluents, durative actions, or `:constants`.

## Example

```
python blackbox.py -o Examples/logistics-strips/domain.pddl \
                   -f Examples/logistics-strips/prob004-log-a.pddl \
                   -i 1 -solver cadical
```
