"""
grounder.py - Ground STRIPS actions from PDDL operator schemas.

Goes directly from parsed PDDL to ground actions without building a
planning graph. For each action schema, enumerates all type-compatible
object combinations to produce GroundAction instances.
"""

from __future__ import annotations
from dataclasses import dataclass, field
from itertools import product
from typing import Optional, Any

CONNECTOR = '_'
DELETE = 'not'
SKIP_HEADS = frozenset({
    '=', 'and', 'or', 'imply', 'when', 'forall', 'exists',
    'increase', 'decrease', 'assign', 'scale-up', 'scale-down',
})


@dataclass(frozen=True)
class GroundAction:
    """A fully ground STRIPS action."""
    name: str
    pos_pre: frozenset   # fluent strings that must be TRUE
    neg_pre: frozenset   # fluent strings that must be FALSE
    add_eff: frozenset   # fluent strings that become TRUE
    del_eff: frozenset   # fluent strings that become FALSE


@dataclass
class _Operator:
    """Lightweight schema for an uninstantiated action."""
    name: str = ""
    params: list = field(default_factory=list)        # variable names  ?x ?y ...
    _param_types: dict = field(default_factory=dict)   # ?var -> type string
    preconds: list = field(default_factory=list)
    effects: list = field(default_factory=list)


class STRIPSProblem:
    """Holds the fully preprocessed STRIPS problem."""

    def __init__(self):
        self.ops: list[_Operator] = []
        self.initial_facts: list[list[str]] = []  # list of token lists
        self.the_goals: list = []
        self.objects: list[str] = []
        self.the_types: dict[str, str] = {}
        self.types_table: dict[str, set[str]] = {}
        self.domain_name: str = ""
        self.problem_name: str = ""
        self.predicates: list = []
        self.constants: list = []
        self.enable_relevance_pruning: bool = True
        self.force_neg: bool = False
        self.debug: int = 0
        # Derived
        self.relevant_predicates: set[str] = set()
        self.negation_predicates: set[str] = set()

    # ── Loading ───────────────────────────────────────────────────────────

    def load(self, domain_file: str, problem_file: str):
        """Parse domain + problem PDDL and populate internal state."""
        from pddl_parser import parse_pddl_file, typed_list_to_objects, typed_list_to_type_map

        domain = parse_pddl_file(domain_file)
        problem = parse_pddl_file(problem_file)

        self.domain_name = domain['name']
        self.problem_name = problem['name']

        for act in domain['actions']:
            op = _Operator()
            op.name = act['name']
            for names, typ in act['params']:
                for n in names:
                    op.params.append(n)
                    if typ:
                        op._param_types[n] = typ
            op.preconds = act['preconds']
            op.effects = act['effects']
            self.ops.append(op)

        self.predicates = domain.get('predicates', [])
        self.constants = domain.get('constants', [])

        obj_groups = problem.get('objects', [])
        self.objects = typed_list_to_objects(obj_groups)
        self.the_types = typed_list_to_type_map(obj_groups)

        for names, typ in self.constants:
            for n in names:
                if n not in self.the_types:
                    self.objects.append(n)
                    self.the_types[n] = typ if typ else 'object'

        # Build types_table (type → set of objects)
        for obj, typ in self.the_types.items():
            if typ and typ.startswith('(either '):
                inner = typ[len('(either '):-1]
                for t in inner.split():
                    self.types_table.setdefault(t.lower(), set()).add(obj)
            else:
                if typ:
                    self.types_table.setdefault(typ, set()).add(obj)
            self.types_table.setdefault('object', set()).add(obj)

        for names, parent in domain.get('types', []):
            for n in names:
                self.types_table.setdefault(n.lower(), set())

        for names, parent in domain.get('types', []):
            parent_type = parent.lower() if parent else 'object'
            for n in names:
                n = n.lower()
                for obj in list(self.types_table.get(n, [])):
                    self.types_table.setdefault(parent_type, set()).add(obj)

        self.initial_facts = problem.get('init', [])
        self.the_goals = problem.get('goal', [])

    # ── Preprocessing ─────────────────────────────────────────────────────

    def process_data(self):
        """Normalize: handle negation predicates and prune irrelevant actions."""
        self._process_negations()
        self._prune_irrelevant_actions()

    def _collect_preds(self, node: Any, out: set[str]):
        """Recursively collect predicate names from a parsed formula."""
        if isinstance(node, list):
            if not node:
                return
            first = node[0]
            if not isinstance(first, str):
                for item in node:
                    self._collect_preds(item, out)
                return
            if first == DELETE:
                if len(node) > 1 and isinstance(node[1], str) and node[1] not in SKIP_HEADS:
                    out.add(node[1])
                for item in node[1:]:
                    self._collect_preds(item, out)
                return
            if first not in SKIP_HEADS:
                out.add(first)
            for item in node[1:]:
                self._collect_preds(item, out)
        elif isinstance(node, dict):
            for v in node.values():
                self._collect_preds(v, out)

    def _prune_irrelevant_actions(self):
        """Backward relevance fixpoint over action schemas."""
        if not self.enable_relevance_pruning or not self.ops:
            return

        goal_preds: set[str] = set()
        self._collect_preds(self.the_goals, goal_preds)

        if not goal_preds:
            return

        op_infos = []
        for op in self.ops:
            add_preds: set[str] = set()
            pre_preds: set[str] = set()
            self._collect_preds(op.effects, add_preds)
            self._collect_preds(op.preconds, pre_preds)
            op_infos.append({
                'op': op,
                'add_preds': add_preds,
                'pre_preds': pre_preds,
                'complex': any(isinstance(x, dict) for x in op.preconds + op.effects),
            })

        relevant = set(goal_preds)
        relevant_idx: set[int] = set()
        changed = True
        while changed:
            changed = False
            for i, info in enumerate(op_infos):
                if i in relevant_idx:
                    continue
                if info['complex'] or (info['add_preds'] & relevant):
                    relevant_idx.add(i)
                    before = len(relevant)
                    relevant |= info['pre_preds']
                    if len(relevant) != before:
                        changed = True
                    changed = True

        old_count = len(self.ops)
        self.ops = [op_infos[i]['op'] for i in range(len(op_infos)) if i in relevant_idx]
        self.relevant_predicates = relevant

        if self.debug >= 1:
            print(f"  Relevance pruning: {old_count} -> {len(self.ops)} schemas, "
                  f"{len(self.relevant_predicates)} predicates")

    def _process_negations(self):
        """Find negation predicates used in goals/preconds (informational)."""
        # Collect negative goal predicates
        for g in self.the_goals:
            if isinstance(g, list) and g and g[0] == DELETE:
                if len(g) > 1:
                    self.negation_predicates.add(g[1])
        # Collect negative precondition predicates
        for op in self.ops:
            for fact in op.preconds:
                if isinstance(fact, list) and fact and fact[0] == DELETE:
                    if len(fact) > 1:
                        self.negation_predicates.add(fact[1])


# ── Grounding ─────────────────────────────────────────────────────────────────

def _objects_for_type(param_type: Optional[str], objects: list[str],
                      types_table: dict[str, set[str]]) -> list[str]:
    """Return valid objects for a typed parameter."""
    if not param_type or param_type == 'object':
        return objects
    return sorted(types_table.get(param_type, set()))


def _collect_effect_predicates(ops: list) -> set[str]:
    """Return the set of predicate names that appear in any operator's effects.

    Predicates that are NOT in this set are "static" — they never change and
    are safe to use as type-based grounding filters.
    """
    effect_preds: set[str] = set()
    for op in ops:
        for fact in op.effects:
            if not isinstance(fact, list) or not fact:
                continue
            head = fact[0]
            if isinstance(head, str):
                if head == DELETE:
                    if len(fact) > 1 and isinstance(fact[1], str):
                        effect_preds.add(fact[1])
                elif head not in SKIP_HEADS:
                    effect_preds.add(head)
    return effect_preds


def _infer_param_types_from_preconds(
    op: _Operator,
    initial_facts: list[list[str]],
    effect_preds: set[str],
) -> dict[str, set[str]]:
    """Infer valid objects per parameter using STATIC unary initial-state predicates.

    For each parameter ?x, finds preconditions of the form (pred ?x) where
    *pred* is a static predicate (never appears in any action effect) and
    restricts ?x to objects that satisfy ALL such unary predicates initially.
    This is "type-based grounding pruning" — major reduction for untyped
    domains that encode types as unary predicates (e.g. the depot domain).

    Only static predicates are used to avoid incorrectly pruning actions based
    on changing fluents (e.g. `clear` in blocksworld).

    Returns a dict: param_var → set of valid objects (empty dict = no constraints).
    """
    # Build initial-state index for STATIC unary predicates: pred → {obj, ...}
    unary_init: dict[str, set[str]] = {}
    for fact in initial_facts:
        if len(fact) == 2 and fact[0] not in (DELETE, '='):
            pred, obj = fact[0], fact[1]
            # Only use this predicate if it is static (not in any action's effects)
            if pred not in effect_preds:
                unary_init.setdefault(pred, set()).add(obj)

    if not unary_init:
        return {}

    # For each param ?x, intersect constraints across all unary static preconditions
    param_valid: dict[str, set[str]] = {}
    for fact in op.preconds:
        if not isinstance(fact, list) or len(fact) != 2:
            continue
        pred, arg = fact[0], fact[1]
        if (isinstance(arg, str) and arg.startswith('?')
                and pred in unary_init and pred not in SKIP_HEADS):
            valid_for_pred = unary_init[pred]
            if arg not in param_valid:
                param_valid[arg] = set(valid_for_pred)
            else:
                param_valid[arg] &= valid_for_pred

    return param_valid


def _instantiate_fluent(tokens: list[str], insts: dict[str, str]) -> Optional[str]:
    """Substitute variables in a fluent token list."""
    parts: list[str] = []
    for t in tokens:
        if t.startswith('?'):
            val = insts.get(t)
            if val is None:
                return None
            parts.append(val)
        else:
            parts.append(t)
    return CONNECTOR.join(parts)


def _parse_formula(formula: Any, insts: dict[str, str],
                   pos_pre: set, neg_pre: set, add_eff: set, del_eff: set,
                   mode: str):
    """
    Recursively parse a precondition/effect formula into pos/neg sets.
    mode: 'pre' for preconditions, 'eff' for effects.
    """
    if isinstance(formula, dict):
        return  # skip quantified/complex
    if not isinstance(formula, list) or not formula:
        return
    head = formula[0] if isinstance(formula[0], str) else None
    if head is None:
        # List of formulas
        for item in formula:
            _parse_formula(item, insts, pos_pre, neg_pre, add_eff, del_eff, mode)
        return

    if head in ('and',):
        for item in formula[1:]:
            _parse_formula(item, insts, pos_pre, neg_pre, add_eff, del_eff, mode)
        return

    if head == DELETE:
        inner = formula[1:]
        if not inner or not isinstance(inner[0], str):
            return
        inner_head = inner[0]
        if inner_head in ('=',):
            # Inequality constraint — handled separately
            return
        if inner_head in SKIP_HEADS:
            return
        fluent = _instantiate_fluent(inner, insts)
        if fluent is None:
            return
        if mode == 'pre':
            neg_pre.add(fluent)
        else:  # eff
            del_eff.add(fluent)
        return

    if head == '=':
        # Equality constraint — skip
        return

    if head in SKIP_HEADS:
        # 'when', 'forall', etc. — skip complex formulas
        return

    # Plain positive fact
    fluent = _instantiate_fluent(formula, insts)
    if fluent is None:
        return
    if mode == 'pre':
        pos_pre.add(fluent)
    else:
        add_eff.add(fluent)


def _check_equality_preconds(preconds: list, insts: dict[str, str]) -> bool:
    """Check equality/inequality constraints in preconditions."""
    for fact in preconds:
        if not isinstance(fact, list) or not fact:
            continue
        head = fact[0]
        if head == '=' and len(fact) == 3:
            a = insts.get(fact[1], fact[1])
            b = insts.get(fact[2], fact[2])
            if a != b:
                return False  # equality violated
        elif head == DELETE and len(fact) >= 2 and isinstance(fact[1], list):
            inner = fact[1]
            if inner and inner[0] == '=' and len(inner) == 3:
                a = insts.get(inner[1], inner[1])
                b = insts.get(inner[2], inner[2])
                if a == b:
                    return False  # inequality violated
        elif head == DELETE and len(fact) == 3 and fact[1] == '=':
            a = insts.get(fact[2], fact[2])
            b = insts.get(fact[3], fact[3]) if len(fact) > 3 else None
            # This format: (not (= ?x ?y)) may come as ['not', '=', ?x, ?y]
            # handled via _check_equality_preconds
    return True


def _instantiate_op(op: _Operator, insts: dict[str, str]) -> Optional[GroundAction]:
    """Instantiate a single operator schema with variable bindings."""
    name_parts = [op.name] + [insts.get(p, p) for p in op.params
                               if p.startswith('?')]
    name = CONNECTOR.join(name_parts)

    pos_pre: set[str] = set()
    neg_pre: set[str] = set()
    add_eff: set[str] = set()
    del_eff: set[str] = set()

    # Check equality constraints in preconditions
    if not _check_equality_preconds(op.preconds, insts):
        return None

    # Parse preconditions
    for fact in op.preconds:
        _parse_formula(fact, insts, pos_pre, neg_pre, add_eff, del_eff, 'pre')

    # Parse effects
    for fact in op.effects:
        _parse_formula(fact, insts, pos_pre, neg_pre, add_eff, del_eff, 'eff')

    # Tautology pruning: skip if add ∩ del or no effects
    if not add_eff and not del_eff:
        return None  # vacuous action

    return GroundAction(
        name=name,
        pos_pre=frozenset(pos_pre),
        neg_pre=frozenset(neg_pre),
        add_eff=frozenset(add_eff),
        del_eff=frozenset(del_eff),
    )


def ground_all_actions(problem: STRIPSProblem) -> list[GroundAction]:
    """Ground all operator schemas against all type-compatible object combos.

    Uses two levels of pruning:
    1. PDDL typed parameters (`:types` section)
    2. STATIC unary initial-state predicates (for untyped domains that encode
       types as predicates, e.g. `(truck ?x)` → only trucks can fill ?x).
       Only predicates that never appear in any action's effects are used, to
       avoid incorrectly pruning based on changing fluents like `clear`.
    """
    ground_actions: list[GroundAction] = []
    seen_names: set[str] = set()

    # Pre-compute the set of predicates that appear in any action's effects.
    # These are "dynamic" and must NOT be used for type-based pruning.
    effect_preds = _collect_effect_predicates(problem.ops)

    for op in problem.ops:
        param_vars = [p for p in op.params if p.startswith('?')]
        if not param_vars:
            ga = _instantiate_op(op, {})
            if ga and ga.name not in seen_names:
                ground_actions.append(ga)
                seen_names.add(ga.name)
            continue

        # Level 1: typed objects from :types declarations
        obj_lists_typed = [
            _objects_for_type(op._param_types.get(pv), problem.objects,
                              problem.types_table)
            for pv in param_vars
        ]

        # Level 2: narrow further using STATIC unary initial-state predicates
        inferred = _infer_param_types_from_preconds(
            op, problem.initial_facts, effect_preds
        )
        obj_lists: list[list[str]] = []
        for pv, typed_objs in zip(param_vars, obj_lists_typed):
            if pv in inferred:
                # Intersect typed with inferred
                inferred_objs = inferred[pv]
                filtered = [o for o in typed_objs if o in inferred_objs]
                obj_lists.append(filtered)
            else:
                obj_lists.append(typed_objs)

        # Skip operators with no valid objects for some parameter
        if any(len(ol) == 0 for ol in obj_lists):
            continue

        for combo in product(*obj_lists):
            insts = dict(zip(param_vars, combo))
            ga = _instantiate_op(op, insts)
            if ga is None:
                continue
            if ga.name in seen_names:
                continue
            ground_actions.append(ga)
            seen_names.add(ga.name)

    return ground_actions


def collect_all_fluents(problem: STRIPSProblem,
                        ground_actions: list[GroundAction]) -> tuple[list[str], set[str], list]:
    """
    Collect all fluents that appear anywhere in the problem.

    Returns:
        all_fluents: sorted list of fluent strings
        initial_set: set of fluents true in initial state
        goal_literals: list of (polarity: bool, fluent_str) pairs
    """
    fluent_set: set[str] = set()

    # From initial facts
    for fact in problem.initial_facts:
        if not fact:
            continue
        if fact[0] == DELETE:
            if len(fact) > 1:
                fluent_set.add(CONNECTOR.join(fact[1:]))
        else:
            fluent_set.add(CONNECTOR.join(fact))

    # From goals (positive and negative)
    goal_literals: list[tuple[bool, str]] = []
    for g in problem.the_goals:
        if not isinstance(g, list) or not g:
            continue
        if g[0] == DELETE:
            if len(g) > 1:
                f = CONNECTOR.join(g[1:])
                fluent_set.add(f)
                goal_literals.append((False, f))
        else:
            f = CONNECTOR.join(g)
            fluent_set.add(f)
            goal_literals.append((True, f))

    # From ground action preconditions and effects
    for ga in ground_actions:
        fluent_set |= ga.pos_pre
        fluent_set |= ga.neg_pre
        fluent_set |= ga.add_eff
        fluent_set |= ga.del_eff

    all_fluents = sorted(fluent_set)

    # Build initial state set
    initial_set: set[str] = set()
    for fact in problem.initial_facts:
        if not fact:
            continue
        if fact[0] != DELETE:
            initial_set.add(CONNECTOR.join(fact))

    return all_fluents, initial_set, goal_literals
