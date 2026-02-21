"""
pddl_parser.py - Recursive descent parser for PDDL domain / problem files.

Replaces: bbpddl.l (flex lexer) + bbpddl.y (bison parser).

No external dependencies -- pure Python tokeniser + parser.
"""

from __future__ import annotations
import re
from dataclasses import dataclass, field
from typing import Optional


# ── Tokeniser ─────────────────────────────────────────────────────────────────

# Token kinds (we only need a handful)
TOK_LPAREN = '('
TOK_RPAREN = ')'
TOK_DASH   = '-'
TOK_COLON  = ':'
TOK_ID     = 'ID'
TOK_VAR    = 'VAR'
TOK_EOF    = 'EOF'

# Matches the flex pattern  [.a-zA-Z0-9_=\-]+
_ID_RE = re.compile(r'[.a-zA-Z0-9_=\-]+')

@dataclass
class Token:
    kind: str
    value: str
    line: int = 0


def tokenize(text: str) -> list[Token]:
    """Tokenise PDDL text (case-insensitive identifiers, ; comments)."""
    tokens: list[Token] = []
    i = 0
    line = 1
    n = len(text)
    while i < n:
        ch = text[i]
        # whitespace
        if ch in ' \t\r':
            i += 1
            continue
        if ch == '\n':
            line += 1
            i += 1
            continue
        # comment
        if ch == ';':
            while i < n and text[i] not in '\r\n':
                i += 1
            continue
        # parens
        if ch == '(':
            tokens.append(Token(TOK_LPAREN, '(', line))
            i += 1
            continue
        if ch == ')':
            tokens.append(Token(TOK_RPAREN, ')', line))
            i += 1
            continue
        # variable  ?id
        if ch == '?':
            j = i + 1
            m = _ID_RE.match(text, j)
            if m:
                val = '?' + m.group(0)
                tokens.append(Token(TOK_VAR, val.lower(), line))
                i = m.end()
            else:
                tokens.append(Token(TOK_VAR, '?', line))
                i = j
            continue
        # colon (keyword prefix) -- the keyword itself is a subsequent ID
        if ch == ':':
            tokens.append(Token(TOK_COLON, ':', line))
            i += 1
            continue
        # dash (type separator) -- only if followed by space/paren/letter
        if ch == '-':
            # peek: if next char is whitespace / paren / letter → it's a dash
            nxt = text[i+1] if i+1 < n else ' '
            if nxt in ' \t\r\n()':
                tokens.append(Token(TOK_DASH, '-', line))
                i += 1
                continue
            # otherwise fall through to ID match (e.g. "loc-from")
        # identifier  [.a-zA-Z0-9_=\-]+
        m = _ID_RE.match(text, i)
        if m:
            tokens.append(Token(TOK_ID, m.group(0).lower(), line))
            i = m.end()
            continue
        # skip unknown
        i += 1
    tokens.append(Token(TOK_EOF, '', line))
    return tokens


# ── Parser ────────────────────────────────────────────────────────────────────

class ParseError(Exception):
    pass


class PDDLParser:
    """Recursive-descent parser for PDDL domain / problem / control files."""

    def __init__(self, tokens: list[Token]):
        self.tokens = tokens
        self.pos = 0

    # -- helpers -------------------------------------------------------------

    def _cur(self) -> Token:
        return self.tokens[self.pos]

    def _peek_kind(self) -> str:
        return self.tokens[self.pos].kind

    def _peek_value(self) -> str:
        return self.tokens[self.pos].value

    def _advance(self) -> Token:
        t = self.tokens[self.pos]
        self.pos += 1
        return t

    def _expect(self, kind: str, value: str | None = None) -> Token:
        t = self._advance()
        if t.kind != kind:
            raise ParseError(
                f"line {t.line}: expected {kind}"
                + (f" '{value}'" if value else "")
                + f", got {t.kind} '{t.value}'"
            )
        if value is not None and t.value != value:
            raise ParseError(
                f"line {t.line}: expected '{value}', got '{t.value}'"
            )
        return t

    def _match(self, kind: str, value: str | None = None) -> bool:
        t = self._cur()
        if t.kind != kind:
            return False
        if value is not None and t.value != value:
            return False
        return True

    def _at_keyword(self, kw: str) -> bool:
        """Check for  :keyword  pattern (colon followed by ID matching *kw*)."""
        if self.pos + 1 >= len(self.tokens):
            return False
        return (self.tokens[self.pos].kind == TOK_COLON
                and self.tokens[self.pos + 1].value == kw)

    def _consume_keyword(self, kw: str):
        self._expect(TOK_COLON)
        self._expect(TOK_ID, kw)

    def _read_id(self) -> str:
        """Read an identifier (ID or VAR or keyword-as-id)."""
        t = self._advance()
        if t.kind in (TOK_ID, TOK_VAR):
            return t.value
        raise ParseError(f"line {t.line}: expected identifier, got {t.kind} '{t.value}'")

    def _skip_term(self):
        """Skip one term: either an atom token or a balanced parenthesised form."""
        if self._match(TOK_LPAREN):
            # _skip_balanced assumes the opening '(' is already consumed.
            self._advance()
            self._skip_balanced()
        else:
            self._advance()

    # -- top level -----------------------------------------------------------

    def parse(self) -> dict:
        """Parse a complete PDDL file and return a result dict.

        Return keys depend on input type:
          domain:  'type'='domain', 'name', 'requirements', 'types', 'constants',
                   'predicates', 'actions'
          problem: 'type'='problem', 'name', 'domain', 'objects', 'init', 'goal',
                   'length'
          control: 'type'='control', ...
        """
        self._expect(TOK_LPAREN)
        self._expect(TOK_ID, 'define')
        self._expect(TOK_LPAREN)
        kind = self._read_id()
        if kind == 'domain':
            result = self._parse_domain()
        elif kind == 'problem':
            result = self._parse_problem()
        elif kind == 'control':
            result = self._parse_control()
        else:
            raise ParseError(f"Unknown PDDL type: {kind}")
        return result

    # -- domain --------------------------------------------------------------

    def _parse_domain(self) -> dict:
        name = self._read_id()
        self._expect(TOK_RPAREN)   # close (domain name)
        result: dict = {
            'type': 'domain',
            'name': name,
            'requirements': [],
            'types': [],
            'constants': [],
            'predicates': [],
            'actions': [],
        }
        while not self._match(TOK_RPAREN):
            self._parse_domain_structure(result)
        self._expect(TOK_RPAREN)   # close (define ...)
        return result

    def _parse_domain_structure(self, result: dict):
        self._expect(TOK_LPAREN)
        if self._at_keyword('requirements'):
            self._consume_keyword('requirements')
            result['requirements'] = self._parse_requirements()
            self._expect(TOK_RPAREN)
        elif self._at_keyword('types'):
            self._consume_keyword('types')
            result['types'] = self._parse_typed_list()
            self._expect(TOK_RPAREN)
        elif self._at_keyword('constants'):
            self._consume_keyword('constants')
            result['constants'] = self._parse_typed_list()
            self._expect(TOK_RPAREN)
        elif self._at_keyword('predicates'):
            self._consume_keyword('predicates')
            result['predicates'] = self._parse_predicate_list()
            self._expect(TOK_RPAREN)
        elif self._at_keyword('action'):
            self._consume_keyword('action')
            result['actions'].append(self._parse_action())
            self._expect(TOK_RPAREN)
        else:
            # skip unknown section
            self._skip_balanced()

    # -- problem -------------------------------------------------------------

    def _parse_problem(self) -> dict:
        name = self._read_id()
        self._expect(TOK_RPAREN)  # close (problem name)
        result: dict = {
            'type': 'problem',
            'name': name,
            'domain': '',
            'objects': [],
            'init': [],
            'goal': [],
            'length': {},
        }
        # (:domain ...)
        self._expect(TOK_LPAREN)
        self._consume_keyword('domain')
        result['domain'] = self._read_id()
        self._expect(TOK_RPAREN)
        while not self._match(TOK_RPAREN):
            self._parse_problem_structure(result)
        self._expect(TOK_RPAREN)
        return result

    def _parse_problem_structure(self, result: dict):
        self._expect(TOK_LPAREN)
        if self._at_keyword('requirements'):
            self._consume_keyword('requirements')
            self._parse_requirements()
            self._expect(TOK_RPAREN)
        elif self._at_keyword('objects'):
            self._consume_keyword('objects')
            result['objects'] = self._parse_typed_list()
            self._expect(TOK_RPAREN)
        elif self._at_keyword('init'):
            self._consume_keyword('init')
            result['init'] = self._parse_fact_list_flat()
            self._expect(TOK_RPAREN)
        elif self._at_keyword('goal'):
            self._consume_keyword('goal')
            result['goal'] = self._parse_formula()
            self._expect(TOK_RPAREN)
        elif self._at_keyword('length'):
            self._consume_keyword('length')
            result['length'] = self._parse_length_spec()
            self._expect(TOK_RPAREN)
        else:
            self._skip_balanced()

    # -- control (stub -- not in scope) ------------------------------------

    def _parse_control(self) -> dict:
        name = self._read_id()
        self._expect(TOK_RPAREN)
        result: dict = {'type': 'control', 'name': name, 'rules': []}
        # skip until closing paren
        depth = 0
        while True:
            if self._match(TOK_RPAREN) and depth == 0:
                break
            if self._match(TOK_LPAREN):
                depth += 1
            elif self._match(TOK_RPAREN):
                depth -= 1
            self._advance()
        self._expect(TOK_RPAREN)
        return result

    # -- requirements -------------------------------------------------------

    def _parse_requirements(self) -> list[str]:
        reqs: list[str] = []
        while self._match(TOK_COLON):
            self._advance()  # consume ':'
            reqs.append(self._read_id())
        return reqs

    # -- typed list  (e.g.  a b c - type  d e - type2  f g) ----------------

    def _parse_typed_list(self) -> list[tuple[list[str], str | None]]:
        """Return list of  (names, type_or_None)  groups."""
        groups: list[tuple[list[str], str | None]] = []
        names: list[str] = []
        while not self._match(TOK_RPAREN):
            if self._match(TOK_DASH):
                self._advance()  # consume '-'
                typ = self._parse_type()
                groups.append((names, typ))
                names = []
            elif self._match(TOK_LPAREN):
                # e.g. a predicate-style entry inside :types
                break
            else:
                names.append(self._read_id())
        if names:
            groups.append((names, None))
        return groups

    def _parse_typed_param_list(self) -> list[tuple[list[str], str | None]]:
        """Like typed_list but items must be variables."""
        groups: list[tuple[list[str], str | None]] = []
        names: list[str] = []
        while not self._match(TOK_RPAREN):
            if self._match(TOK_DASH):
                self._advance()
                typ = self._parse_type()
                groups.append((names, typ))
                names = []
            else:
                names.append(self._read_id())
        if names:
            groups.append((names, None))
        return groups

    def _parse_type(self) -> str:
        """Parse a type: simple id or  (either t1 t2 ...)."""
        if self._match(TOK_LPAREN):
            self._advance()  # (
            self._expect(TOK_ID, 'either')
            types: list[str] = []
            while not self._match(TOK_RPAREN):
                types.append(self._read_id())
            self._advance()  # )
            return '(either ' + ' '.join(types) + ')'
        return self._read_id()

    # -- predicates ---------------------------------------------------------

    def _parse_predicate_list(self) -> list[dict]:
        """Return list of  {name, params: typed_param_list}."""
        preds: list[dict] = []
        while self._match(TOK_LPAREN):
            self._advance()  # (
            name = self._read_id()
            params = self._parse_typed_param_list()
            self._expect(TOK_RPAREN)
            preds.append({'name': name, 'params': params})
        return preds

    # -- action -------------------------------------------------------------

    def _parse_action(self) -> dict:
        name = self._read_id()
        params: list = []
        preconds: list = []
        effects: list = []
        while not self._match(TOK_RPAREN):
            if self._at_keyword('parameters'):
                self._consume_keyword('parameters')
                self._expect(TOK_LPAREN)
                params = self._parse_typed_param_list()
                self._expect(TOK_RPAREN)
            elif self._at_keyword('precondition'):
                self._consume_keyword('precondition')
                preconds = self._parse_formula()
            elif self._at_keyword('effect'):
                self._consume_keyword('effect')
                effects = self._parse_formula()
            else:
                # skip unknown keyword
                self._advance()
        return {'name': name, 'params': params, 'preconds': preconds, 'effects': effects}

    # -- formula / fact list ------------------------------------------------

    def _parse_formula(self) -> list[list[str]]:
        """Parse a goal/precondition/effect formula.

        Returns a flat list of *fact tuples* (each a list[str]).
        ``(and f1 f2 ...)`` is flattened; ``(not (p x))`` becomes
        ``['not', 'p', 'x']``.
        """
        if self._match(TOK_LPAREN):
            self._advance()  # (
            # empty
            if self._match(TOK_RPAREN):
                self._advance()
                return []
            first = self._peek_value()
            if first == 'and':
                self._advance()  # consume 'and'
                facts: list[list[str]] = []
                while not self._match(TOK_RPAREN):
                    facts.extend(self._parse_formula())
                self._advance()  # )
                return facts
            elif first == 'not':
                self._advance()  # consume 'not'
                inner = self._parse_single_fact()
                self._expect(TOK_RPAREN)
                return [['not'] + inner]
            elif first == 'forall':
                return self._parse_quantified('forall')
            elif first == 'exists':
                return self._parse_quantified('exists')
            elif first in ('increase', 'decrease', 'assign', 'scale-up', 'scale-down', '='):
                # Numeric/function effect/precondition; not used by STRIPS GraphPlan.
                self._advance()  # consume keyword
                while not self._match(TOK_RPAREN):
                    self._skip_term()
                self._advance()  # )
                return []
            else:
                # plain atom  (pred arg1 arg2 ...)
                tokens: list[str] = []
                saw_nested = False
                while not self._match(TOK_RPAREN):
                    if self._match(TOK_LPAREN):
                        saw_nested = True
                        self._skip_term()
                    else:
                        tokens.append(self._read_id())
                self._advance()  # )
                if saw_nested:
                    # Skip non-atomic terms such as (= (total-cost) 0).
                    return []
                return [tokens]
        else:
            # bare id (unusual but handle)
            return [[self._read_id()]]

    def _parse_single_fact(self) -> list[str]:
        """Parse one atomic fact ``(pred a1 a2 ...)`` and return token list."""
        self._expect(TOK_LPAREN)
        tokens: list[str] = []
        while not self._match(TOK_RPAREN):
            tokens.append(self._read_id())
        self._expect(TOK_RPAREN)
        return tokens

    def _parse_quantified(self, kind: str) -> list[list[str]]:
        """Parse  (forall/exists (?v - type) formula formula) ."""
        self._advance()  # consume 'forall'/'exists'
        self._expect(TOK_LPAREN)
        params = self._parse_typed_param_list()
        self._expect(TOK_RPAREN)
        # Read the scope term and body
        scope = self._parse_formula()
        body = self._parse_formula() if not self._match(TOK_RPAREN) else []
        self._expect(TOK_RPAREN)
        # Encode as special fact: [kind, params_encoded, scope, body]
        return [{'quantifier': kind, 'params': params, 'scope': scope, 'body': body}]

    def _parse_fact_list_flat(self) -> list[list[str]]:
        """Parse a list of ground atoms (no 'and' wrapper) for :init."""
        facts: list[list[str]] = []
        while self._match(TOK_LPAREN):
            self._advance()  # (
            first_val = self._peek_value()
            if first_val == 'not':
                self._advance()
                inner = self._parse_single_fact()
                facts.append(['not'] + inner)
                self._expect(TOK_RPAREN)
            elif first_val in ('=', 'increase', 'decrease', 'assign', 'scale-up', 'scale-down'):
                # Ignore numeric/function assignments in :init for STRIPS planner.
                self._advance()
                while not self._match(TOK_RPAREN):
                    self._skip_term()
                self._expect(TOK_RPAREN)
            else:
                tokens: list[str] = []
                saw_nested = False
                while not self._match(TOK_RPAREN):
                    if self._match(TOK_LPAREN):
                        saw_nested = True
                        self._skip_term()
                    else:
                        tokens.append(self._read_id())
                self._advance()  # )
                if not saw_nested:
                    facts.append(tokens)
        return facts

    # -- length spec --------------------------------------------------------

    def _parse_length_spec(self) -> dict:
        """Parse length spec: ``:serial N :parallel N`` or
        ``(:parallel N) (:serial N)``."""
        spec: dict = {}
        while not self._match(TOK_RPAREN):
            if self._match(TOK_LPAREN):
                # (:parallel N) or (:serial N) form
                self._advance()  # (
                if self._match(TOK_COLON):
                    self._advance()
                kw = self._read_id()
                val = self._read_id()
                spec[kw] = int(val)
                self._expect(TOK_RPAREN)
            elif self._match(TOK_COLON):
                self._advance()
                kw = self._read_id()
                val = self._read_id()
                spec[kw] = int(val)
            else:
                self._advance()  # skip unknown
        return spec

    # -- skip ---------------------------------------------------------------

    def _skip_balanced(self):
        """Skip tokens until the matching ')' for the '(' already consumed."""
        depth = 1
        while depth > 0:
            t = self._advance()
            if t.kind == TOK_LPAREN:
                depth += 1
            elif t.kind == TOK_RPAREN:
                depth -= 1
            elif t.kind == TOK_EOF:
                raise ParseError("Unexpected EOF while skipping")


# ── Public helpers ────────────────────────────────────────────────────────────

def parse_pddl_file(path: str) -> dict:
    """Convenience: read a file, tokenise, parse, return dict."""
    with open(path) as f:
        text = f.read()
    tokens = tokenize(text)
    return PDDLParser(tokens).parse()


def typed_list_to_objects(groups: list[tuple[list[str], str | None]]) -> list[str]:
    """Flatten a typed list into a plain list of object names."""
    result: list[str] = []
    for names, _ in groups:
        result.extend(names)
    return result


def typed_list_to_type_map(groups: list[tuple[list[str], str | None]]) -> dict[str, str]:
    """Convert a typed list to a  name→type  mapping."""
    result: dict[str, str] = {}
    for names, typ in groups:
        for n in names:
            result[n] = typ if typ else 'object'
    return result
