"""
strips_encoder.py - Direct STRIPS to CNF SAT encoding.

Encodes a grounded STRIPS planning problem as a CNF formula without
building an intermediate planning graph.

Encoding (exists-step / parallel semantics):
  Variables:
    fluent(f, t)  - fluent f is true at time t   (t = 0 .. T)
    action(a, t)  - action a executes at time t   (t = 0 .. T-1)

  Clauses:
    1. Initial state (closed world): [+f_0] or [-f_0] for every fluent
    2. Goal state: [+f_T] or [-f_T] for each goal
    3. Preconditions:  ¬a_t ∨ f_t  (pos pre)  and  ¬a_t ∨ ¬f_t  (neg pre)
    4. Effects:        ¬a_t ∨ f_{t+1}  (add)   and  ¬a_t ∨ ¬f_{t+1}  (del)
    5. Explanatory frame axioms:
         ¬f_{t+1} ∨ f_t ∨ (∨ adders_of_f)     (f becomes true)
         f_{t+1} ∨ ¬f_t ∨ (∨ deleters_of_f)   (f becomes false)
    6. Mutex (action interference):
         ¬a1_t ∨ ¬a2_t  for incompatible action pairs (exists-step)

Optimisations carried over from blackbox_python:
  - AMO ladder encoding for mutex cliques (3(k-1) clauses vs k(k-1)/2)
  - Incremental SAT: only encodes new time layers when horizon grows
  - Goal assumptions: goal clauses encoded as SAT assumptions for incremental
  - Relevance-based action pruning (done in grounder, not here)
  - Action minimisation via PySAT cardinality constraints (in planner)
"""

from __future__ import annotations
from typing import Optional
from grounder import GroundAction

# Print flags
PrintLit = 1
PrintCNF = 2
PrintModel = 16


class STRIPSEncoder:
    """Encodes a grounded STRIPS problem as a CNF formula."""

    def __init__(self, ground_actions: list[GroundAction],
                 all_fluents: list[str],
                 initial_set: set[str],
                 goal_literals: list[tuple[bool, str]],
                 printflag: int = 0,
                 exists_step: bool = True,
                 emit_effects: bool = True,
                 emit_mutex: bool = True,
                 close_world: bool = True):
        """
        Parameters
        ----------
        ground_actions: list of GroundAction
        all_fluents:    sorted list of all fluent names
        initial_set:    set of fluents true at t=0
        goal_literals:  list of (polarity, fluent) - goal conditions
        printflag:      debug print flags
        exists_step:    if True use exists-step mutex semantics (default True)
        emit_effects:   if True emit action→effect clauses (default True)
        emit_mutex:     if True emit mutex constraints (default True)
        close_world:    if True assert CWA at t=0 (default True)
        """
        self.ground_actions = ground_actions
        self.all_fluents = all_fluents
        self.initial_set = initial_set
        self.goal_literals = goal_literals
        self.printflag = printflag
        self.exists_step = exists_step
        self.emit_effects = emit_effects
        self.emit_mutex = emit_mutex
        self.close_world = close_world

        # Fluent index (name → index into all_fluents)
        self._fluent_idx: dict[str, int] = {f: i for i, f in enumerate(all_fluents)}
        self._num_fluents = len(all_fluents)
        self._num_actions = len(ground_actions)

        # Action index (name → index into ground_actions)
        self._action_idx: dict[str, int] = {a.name: i for i, a in enumerate(ground_actions)}

        # Variable counters
        self.numvar: int = 0
        self.clauses: list[list[int]] = []
        self.numclause: int = 0
        self.goal_assumptions: list[int] = []

        # For incremental mode: track the last encoded horizon
        self._prev_maxtime: int = 0
        # Variables allocated so far per layer
        # fluent_var[t][fi] and action_var[t][ai]
        self._fluent_vars: list[Optional[list[int]]] = []   # [t][fi] → var
        self._action_vars: list[Optional[list[int]]] = []   # [t][ai] → var

        # Precomputed: for each fluent fi, lists of action indices that add/delete it
        self._adders: list[list[int]] = [[] for _ in range(self._num_fluents)]
        self._deleters: list[list[int]] = [[] for _ in range(self._num_fluents)]
        self._precompute_action_maps()

        # Precomputed mutex pairs (exist-step or forall-step)
        self._mutex_pairs: list[tuple[int, int]] = []
        self._precompute_mutexes()

        # prop2name for debug output
        self._prop2name: list[Optional[str]] = [None]  # 1-indexed

    def _precompute_action_maps(self):
        """Build adders/deleters maps for each fluent."""
        for ai, ga in enumerate(self.ground_actions):
            for f in ga.add_eff:
                fi = self._fluent_idx.get(f)
                if fi is not None:
                    self._adders[fi].append(ai)
            for f in ga.del_eff:
                fi = self._fluent_idx.get(f)
                if fi is not None:
                    self._deleters[fi].append(ai)

    def _precompute_mutexes(self):
        """Compute which action pairs are mutually exclusive."""
        actions = self.ground_actions
        n = len(actions)
        mutex_set: set[tuple[int, int]] = set()

        for i in range(n):
            a = actions[i]
            for j in range(i + 1, n):
                b = actions[j]
                if self._are_mutex(a, b):
                    mutex_set.add((i, j))

        self._mutex_pairs = list(mutex_set)

    def _are_mutex(self, a: GroundAction, b: GroundAction) -> bool:
        """Check if two actions are mutex (exists-step or forall-step).

        Exists-step: mutex iff BOTH sequential orderings are inapplicable.
        "a then b" fails when b's preconditions are violated after a executes:
          - a deletes a positive precondition of b
          - a adds a negative precondition of b
        Conflicting effects (a deletes what b adds, etc.) do NOT make a
        sequential ordering fail in exists-step semantics.
        """
        def a_then_b_fails():
            if a.del_eff & b.pos_pre:
                return True
            if a.add_eff & b.neg_pre:
                return True
            return False

        def b_then_a_fails():
            if b.del_eff & a.pos_pre:
                return True
            if b.add_eff & a.neg_pre:
                return True
            return False

        if self.exists_step:
            # Mutex only if BOTH orderings fail
            return a_then_b_fails() and b_then_a_fails()
        else:
            # Forall-step: mutex if EITHER ordering fails
            return a_then_b_fails() or b_then_a_fails()

    # ── Variable allocation ───────────────────────────────────────────────

    def _alloc_var(self, name: str) -> int:
        self.numvar += 1
        self._prop2name.append(name)
        return self.numvar

    def _fluent_var(self, fi: int, t: int) -> int:
        """Return the SAT variable for fluent fi at time t."""
        return self._fluent_vars[t][fi]

    def _action_var(self, ai: int, t: int) -> int:
        """Return the SAT variable for action ai at time t."""
        return self._action_vars[t][ai]

    def _ensure_vars_allocated(self, maxtime: int, start_from: int = 0):
        """Allocate SAT variables for all layers from start_from to maxtime."""
        # Extend lists if needed
        while len(self._fluent_vars) <= maxtime:
            self._fluent_vars.append(None)
        while len(self._action_vars) <= maxtime:
            self._action_vars.append(None)

        # Fluent vars for layers 0..maxtime
        for t in range(start_from, maxtime + 1):
            if self._fluent_vars[t] is None:
                self._fluent_vars[t] = [
                    self._alloc_var(f"{f}@{t}")
                    for f in self.all_fluents
                ]

        # Action vars for layers 0..maxtime-1
        for t in range(start_from, maxtime):
            if self._action_vars[t] is None:
                self._action_vars[t] = [
                    self._alloc_var(f"{a.name}@{t}")
                    for a in self.ground_actions
                ]

    # ── Main encode ──────────────────────────────────────────────────────

    def encode(self, maxtime: int,
               incremental: bool = False) -> tuple[list[list[int]], int, int]:
        """Encode planning problem to CNF for horizon *maxtime*.

        Returns ``(clauses, numvar, numclause)`` where clauses is a list of
        integer literal lists (positive = true, negative = false).
        In incremental mode, only newly generated clauses are returned.
        """
        self.clauses = []
        self.goal_assumptions = []

        start_layer = self._prev_maxtime if incremental else 0

        if not incremental:
            # Full reset
            self.numvar = 0
            self._prop2name = [None]
            self._fluent_vars = []
            self._action_vars = []
            self._prev_maxtime = 0
            start_layer = 0

        # Allocate variables for new layers
        self._ensure_vars_allocated(maxtime, start_from=start_layer)

        # Initial state (only on first call, or non-incremental)
        if not incremental or self._prev_maxtime == 0:
            self._generate_initial_state()

        # Per-layer clauses (skip already-encoded layers in incremental mode)
        for t in range(start_layer, maxtime):
            self._generate_preconditions(t)
            if self.emit_effects:
                self._generate_effects(t)
            self._generate_frame_axioms(t, simplified=(t == maxtime - 1 and not incremental))
            if self.emit_mutex:
                self._generate_mutex(t)

        # Goal
        if incremental:
            # Return goals as assumptions, not hard clauses
            for polarity, f in self.goal_literals:
                fi = self._fluent_idx.get(f)
                if fi is None:
                    continue
                v = self._fluent_var(fi, maxtime)
                self.goal_assumptions.append(v if polarity else -v)
        else:
            self._generate_goal(maxtime)

        if incremental:
            self._prev_maxtime = maxtime

        self.numclause = len(self.clauses)
        return self.clauses, self.numvar, self.numclause

    # ── Clause generators ─────────────────────────────────────────────────

    def _generate_initial_state(self):
        """Emit unit clauses for initial state (closed world assumption)."""
        for fi, f in enumerate(self.all_fluents):
            v = self._fluent_var(fi, 0)
            if f in self.initial_set:
                self.clauses.append([v])
            elif self.close_world:
                self.clauses.append([-v])

    def _generate_goal(self, maxtime: int):
        """Emit unit clauses for goals at final time step."""
        for polarity, f in self.goal_literals:
            fi = self._fluent_idx.get(f)
            if fi is None:
                continue
            v = self._fluent_var(fi, maxtime)
            self.clauses.append([v if polarity else -v])

    def _generate_preconditions(self, t: int):
        """Emit action→precondition implication clauses at time t."""
        for ai, ga in enumerate(self.ground_actions):
            av = self._action_var(ai, t)
            for f in ga.pos_pre:
                fi = self._fluent_idx.get(f)
                if fi is None:
                    continue
                fv = self._fluent_var(fi, t)
                self.clauses.append([-av, fv])
            for f in ga.neg_pre:
                fi = self._fluent_idx.get(f)
                if fi is None:
                    continue
                fv = self._fluent_var(fi, t)
                self.clauses.append([-av, -fv])

    def _generate_effects(self, t: int):
        """Emit action→effect implication clauses at time t."""
        for ai, ga in enumerate(self.ground_actions):
            av = self._action_var(ai, t)
            for f in ga.add_eff:
                fi = self._fluent_idx.get(f)
                if fi is None:
                    continue
                fv = self._fluent_var(fi, t + 1)
                self.clauses.append([-av, fv])
            for f in ga.del_eff:
                fi = self._fluent_idx.get(f)
                if fi is None:
                    continue
                fv = self._fluent_var(fi, t + 1)
                self.clauses.append([-av, -fv])

    def _generate_frame_axioms(self, t: int, simplified: bool = False):
        """Emit explanatory frame axioms for each fluent at time step t."""
        for fi, f in enumerate(self.all_fluents):
            fv_cur = self._fluent_var(fi, t)
            fv_next = self._fluent_var(fi, t + 1)

            # f becomes TRUE: ¬f_{t+1} ∨ f_t ∨ (∨ adders_t)
            adder_avs = [self._action_var(ai, t) for ai in self._adders[fi]]
            if adder_avs:
                if simplified:
                    # Last layer: ¬f_t ∨ f_{t+1} is handled by CWA / goal
                    # Simplified: just ensure if f true at T, some adder ran
                    # or f was already true. This is the standard frame clause.
                    clause = [-fv_next, fv_cur] + adder_avs
                else:
                    clause = [-fv_next, fv_cur] + adder_avs
                self.clauses.append(clause)
            else:
                # No adder: f can only persist (not become newly true)
                # ¬f_{t+1} ∨ f_t
                self.clauses.append([-fv_next, fv_cur])

            # f becomes FALSE: f_{t+1} ∨ ¬f_t ∨ (∨ deleters_t)
            deleter_avs = [self._action_var(ai, t) for ai in self._deleters[fi]]
            if deleter_avs:
                clause = [fv_next, -fv_cur] + deleter_avs
                self.clauses.append(clause)
            else:
                # No deleter: f can only persist (not become newly false)
                # f_{t+1} ∨ ¬f_t
                self.clauses.append([fv_next, -fv_cur])

    # ── Mutex generation ─────────────────────────────────────────────────

    def _generate_mutex(self, t: int):
        """Emit mutex constraints for action pairs at time t, using AMO ladder."""
        # Build adjacency for clique finding
        n = len(self.ground_actions)
        if n == 0:
            return

        # Group mutexes by clique for AMO encoding
        adj: list[set[int]] = [set() for _ in range(n)]
        for i, j in self._mutex_pairs:
            adj[i].add(j)
            adj[j].add(i)

        # Greedy clique cover
        cliques, leftover = _find_mutex_cliques(n, adj)

        for clique in cliques:
            lits = [self._action_var(ai, t) for ai in clique]
            self._amo_ladder(lits)

        for i, j in leftover:
            av_i = self._action_var(i, t)
            av_j = self._action_var(j, t)
            self.clauses.append([-av_i, -av_j])

    def _amo_ladder(self, lits: list[int]):
        """At-most-one via ladder encoding. O(k) clauses, O(k) aux vars."""
        k = len(lits)
        if k <= 1:
            return
        if k <= 3:
            for i in range(k):
                for j in range(i + 1, k):
                    self.clauses.append([-lits[i], -lits[j]])
            return

        aux = [self._alloc_var(f"amo_aux_{self.numvar}") for _ in range(k - 1)]

        self.clauses.append([-lits[0], aux[0]])
        for i in range(1, k - 1):
            self.clauses.append([-lits[i], aux[i]])
            self.clauses.append([-aux[i - 1], aux[i]])
            self.clauses.append([-lits[i], -aux[i - 1]])
        self.clauses.append([-lits[k - 1], -aux[k - 2]])

    # ── Helpers ──────────────────────────────────────────────────────────

    def get_goal_assumptions(self) -> list[int]:
        """Return goal literals for assumption-based solving."""
        return list(self.goal_assumptions)

    def get_action_vars_at(self, t: int) -> list[int]:
        """Return list of action SAT variable numbers at time t."""
        if t >= len(self._action_vars) or self._action_vars[t] is None:
            return []
        return list(self._action_vars[t])

    def extract_plan(self, soln: list[int], maxtime: int) -> list[list[str]]:
        """Extract plan from SAT solution.

        Returns list of per-step action name lists.
        soln is 1-indexed (soln[0] unused); soln[i] = 1 if var i is True.
        """
        plan: list[list[str]] = []
        for t in range(maxtime):
            step: list[str] = []
            if t < len(self._action_vars) and self._action_vars[t] is not None:
                for ai, av in enumerate(self._action_vars[t]):
                    if av < len(soln) and soln[av] == 1:
                        step.append(self.ground_actions[ai].name)
            plan.append(step)
        return plan

    def to_dimacs(self) -> str:
        """Return DIMACS CNF string (for debugging)."""
        lines = [f"p cnf {self.numvar} {self.numclause}"]
        for clause in self.clauses:
            lines.append(' '.join(str(lit) for lit in clause) + ' 0')
        return '\n'.join(lines) + '\n'

    def print_variable_map(self):
        """Print variable number → name mapping."""
        for i in range(1, self.numvar + 1):
            if i < len(self._prop2name) and self._prop2name[i] is not None:
                print(f"  {i}: {self._prop2name[i]}")


# ── Clique finding for AMO ────────────────────────────────────────────────────

def _find_mutex_cliques(n: int,
                        adj: list[set[int]]) -> tuple[list[list[int]], list[tuple[int, int]]]:
    """Greedy clique cover over the mutex graph. Returns (cliques, leftover_edges)."""
    all_edges: set[tuple[int, int]] = set()
    for i in range(n):
        for j in adj[i]:
            if j > i:
                all_edges.add((i, j))

    covered: set[tuple[int, int]] = set()
    cliques: list[list[int]] = []
    remaining = {i for i in range(n) if adj[i]}

    while remaining:
        seed = max(remaining, key=lambda x: len(adj[x] & remaining))
        if not (adj[seed] & remaining):
            break

        clique = [seed]
        candidates = adj[seed] & remaining
        for c in sorted(candidates, key=lambda x: -len(adj[x] & candidates)):
            if all(c in adj[m] for m in clique):
                clique.append(c)

        if len(clique) < 2:
            break

        for a in range(len(clique)):
            for b in range(a + 1, len(clique)):
                covered.add((min(clique[a], clique[b]), max(clique[a], clique[b])))

        cliques.append(clique)
        for m in clique:
            remaining.discard(m)

    leftover = [e for e in all_edges if e not in covered]
    return cliques, leftover
