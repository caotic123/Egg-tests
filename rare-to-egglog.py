#!/usr/bin/env python3
"""
parser_rare_rules.py – parse `(declare-rare-rule …)` blocks.

Usage:
    python parser_rare_rules.py < rules.txt
or
    rules = parse_rare_rules(source_string)
"""
from __future__ import annotations
from collections import deque, defaultdict
from dataclasses import dataclass, field
from typing import List, Union, Iterator, Tuple
from typing import Iterable, List, Set, Union
from io import StringIO
import re

# --------------------------------------------------------------------------- #
# 1.  Tokeniser & generic S‑expression reader
# --------------------------------------------------------------------------- #

def _tokenise(text: str) -> Iterator[str]:
    """Yield one token at a time (parentheses or atoms)."""
    atom = []
    for ch in text:
        if ch in '()':
            if atom:
                yield ''.join(atom)
                atom.clear()
            yield ch
        elif ch.isspace():
            if atom:
                yield ''.join(atom)
                atom.clear()
        else:
            atom.append(ch)
    if atom:
        yield ''.join(atom)


def _read_sexpr(tokens: Iterator[str]) -> Union[str, List]:
    """Recursive descent into a nested Python list."""
    tok = next(tokens)            # StopIteration bubbles up to caller
    if tok != '(':
        return tok                # atom
    lst = []
    for tok in tokens:
        print(tok)
        if tok == ')':
            return lst
        tokens = _prepend(tok, tokens)  # unread token
        lst.append(_read_sexpr(tokens))
    raise SyntaxError("unbalanced '('")


def _prepend(item, iterator):
    """Put *item* back in front of *iterator*."""
    yield item
    yield from iterator


def parse_sexpressions(text: str) -> List:
    """
    Return a list of top‑level S‑expressions (as Python atoms / nested lists).

    The implementation is now deque‑based and therefore immune to the
    push‑back bug that produced the 'unbalanced (' traceback.
    """
    toks = deque(_tokenise(text))

    def read() -> Union[str, List]:
        if not toks:
            raise SyntaxError("Unexpected end of input")

        tok = toks.popleft()
        if tok != '(':
            return tok                      # atom

        lst = []
        while True:
            if not toks:
                raise SyntaxError("unbalanced '('")
            if toks[0] == ')':             # look‑ahead without consuming
                toks.popleft()             # discard the ')'
                return lst
            lst.append(read())             # recurse on sub‑expr

    exprs = []
    while toks:
        exprs.append(read())
    return exprs

# --------------------------------------------------------------------------- #
# 2.  Domain objects
# --------------------------------------------------------------------------- #

@dataclass
class Parameter:
    name: str
    typ: str
    is_list: bool = False

    @classmethod
    def from_sexpr(cls, sexpr: List[str]) -> 'Parameter':
        if len(sexpr) not in (2, 3):
            raise ValueError(f"Bad parameter form: {sexpr}")
        name, typ, *rest = sexpr
        is_list = bool(rest and rest[0] == ':list')
        return cls(name=name, typ=typ, is_list=is_list)

@dataclass
class RareRule:
    name: str
    parameters: List[Parameter] = field(default_factory=list)
    args: List[str] = field(default_factory=list)
    premises: List[Union[str, List]] = field(default_factory=list)
    conclusion: Union[str, List, None] = None

    @classmethod
    def from_sexpr(cls, sexpr: List) -> 'RareRule':
        if len(sexpr) < 2 or sexpr[0] != 'declare-rare-rule':
            raise ValueError("Not a declare-rare-rule block")

        name = sexpr[1]
        params_raw, *body = sexpr[2:]
        parameters = [Parameter.from_sexpr(p) for p in params_raw]

        args, premises, conclusion = [], [], None
        body_iter = iter(body)
        for key, val in zip(body_iter, body_iter):
            if key == ':args':
                args = val
            elif key == ':premises':
                premises = val
            elif key == ':conclusion':
                conclusion = val
            else:
                raise ValueError(f"Unknown key {key} in rule {name}")

        return cls(name, parameters, args, premises, conclusion)


# --------------------------------------------------------------------------- #
# 3.  High‑level helper
# --------------------------------------------------------------------------- #

def parse_rare_rules(text: str) -> List[RareRule]:
    """Parse *text* and return a list of RareRule objects."""
    rules = []
    for expr in parse_sexpressions(text):
        if isinstance(expr, list) and expr and expr[0] == 'declare-rare-rule':
            rules.append(RareRule.from_sexpr(expr))
    return rules


PREFIX      = "rare"
INT_LITERAL = re.compile(r"^-?\d+$")

# ──────────────────────────────────────────── prefix util
def p(name: str) -> str:
    return name if name.startswith(f"{PREFIX}-") else f"{PREFIX}-{name}"

# ──────────────────────────────────────────── canonical sort
def _canon_sort(raw) -> str:
    if raw is None or isinstance(raw, list) or (isinstance(raw, str) and raw.startswith("@")):
        return "Val"
    low = raw.lower()
    if low == "bool":
        return "Bool"
    if low in {"int", "i32", "i64", "integer"}:
        return "i64"
    return "Val"

# ──────────────────────────────────────────── discovery pass
class _SigInfo:
    """Track argument sorts and whether result appears in Bool context."""
    def __init__(self):
        self.arg_sorts: Set[Tuple[str, ...]] = set()
        self.bool_result: bool = True   # start optimistic

    def add(self, sorts: Tuple[str, ...]):
        self.arg_sorts.add(sorts)

    def mark_non_bool(self):
        self.bool_result = False

def _discover(rules: Iterable["RareRule"]) -> Tuple[Dict[str, _SigInfo], bool]:
    sigs: Dict[str, _SigInfo] = defaultdict(_SigInfo)
    uses_bool = False

    for rr in rules:
        param_ty = {p_.name: _canon_sort(p_.typ) for p_ in rr.parameters}

        # helper: record head + arg sorts
        def record(head, arg_sorts):
            sigs[head].add(tuple(arg_sorts))

        def walk(expr, in_bool_ctx=False):
            nonlocal uses_bool
            if isinstance(expr, list) and expr:
                head, *args = expr
                if isinstance(head, str):
                    arg_sorts: List[str] = []
                    for a in args:
                        if isinstance(a, list):
                            arg_sorts.append("Val")
                            walk(a)
                        elif isinstance(a, str):
                            if a in param_ty:
                                arg_sorts.append(param_ty[a])
                            elif a.lower() in {"true", "false"}:
                                arg_sorts.append("Bool")
                                uses_bool = True
                            elif INT_LITERAL.match(a):
                                arg_sorts.append("i64")
                            else:
                                arg_sorts.append("Val")
                        else:
                            arg_sorts.append("Val")
                    record(head, arg_sorts)
                    # by default we don't know result sort; update below.
                    # equality special case to mark boolean context
                    if head == "=" and len(args) == 2:
                        walk(args[0], in_bool_ctx=True)
                        walk(args[1], in_bool_ctx=True)
                    else:
                        walk(head, False)
                # recurse positional args too
                for sub in args:
                    walk(sub)
            elif isinstance(expr, list):
                for sub in expr:
                    walk(sub)
            elif isinstance(expr, str):
                # If we are inside Bool equality, literals mark Bool use.
                if in_bool_ctx and expr in sigs:
                    sigs[expr].mark_non_bool()

        walk(rr.conclusion)
        for prem in rr.premises:
            walk(prem)

    sigs.pop("=", None)
    return sigs, uses_bool

# ──────────────────────────────────────────── rename map
def _mk_rename_map(heads: Set[str], uses_bool: bool) -> Dict[str, str]:
    rename = {h: p(h) for h in heads}
    if uses_bool:
        rename.update({"True": p("True"), "False": p("False")})
    return rename

# ──────────────────────────────────────────── prelude generation
def _prelude(sigs: Dict[str, _SigInfo], uses_bool: bool) -> str:
    buf = StringIO()
    buf.write(";; ===== Auto‑generated ‘rare’ prelude =====\n")
    if uses_bool:
        buf.write(f"(datatype {p('Bool')} ({p('True')}) ({p('False')}))\n")

    # need rare-Val if any arg or result uses it
    need_val = any(
        "Val" in sorts or not info.bool_result
        for info in sigs.values()
        for sorts in info.arg_sorts
    )
    if need_val:
        buf.write(
            f"(datatype {p('Val')} ({p('MkInt')} i64) ({p('MkBool')} {p('Bool')}))\n"
        )

    for op, info in sorted(sigs.items()):
        arg_sig = max(info.arg_sorts, key=len)  # widest arity
        params = " ".join(
            p("Bool") if s == "Bool" else
            "i64"     if s == "i64"  else
            p("Val")
            for s in arg_sig
        )
        ret_sort = p("Bool") if info.bool_result and uses_bool else p("Val")
        buf.write(f"(function {p(op)} ({params}) {ret_sort} :no-merge)\n")
    buf.write(";; =========================================\n\n")
    return buf.getvalue()

# ──────────────────────────────────────────── pretty‑printing helpers
def _varset(rr) -> Set[str]:
    return {pr.name for pr in rr.parameters} | set(rr.args)

def _atom(tok: str, vset: Set[str], rename: Dict[str, str]) -> str:
    if tok in vset:
        return f"?{tok}"
    if tok.lower() == "true":
        return rename["True"]
    if tok.lower() == "false":
        return rename["False"]
    return rename.get(tok, tok)

def _pp(expr: Union[str, List], vset: Set[str], rename: Dict[str, str]) -> str:
    if isinstance(expr, list):
        return "(" + " ".join(_pp(e, vset, rename) for e in expr) + ")"
    return _atom(expr, vset, rename)

def _free_vars(expr: Union[str, List], vset: Set[str]) -> Set[str]:
    acc: Set[str] = set()
    def walk(e):
        if isinstance(e, list):
            for sub in e:
                walk(sub)
        elif isinstance(e, str) and e in vset:
            acc.add(e)
    walk(expr)
    return acc

# ──────────────────────────────────────────── encode rule / rewrite
def _encode_rule(rr: "RareRule", rename: Dict[str, str]) -> str:
    vset = _varset(rr)
    concl = rr.conclusion
    if concl is None:
        raise ValueError(f"{rr.name}: empty conclusion")

    is_eq = isinstance(concl, list) and len(concl) == 3 and concl[0] == "="
    lhs, rhs = (concl[1], concl[2]) if is_eq else (None, None)

    prems_pp = [_pp(p, vset, rename) for p in rr.premises]
    vars_body = set().union(*(_free_vars(p, vset) for p in rr.premises)) if prems_pp else set()

    def as_rewrite(guard: List[str] = None) -> str:
        lpp, rpp = _pp(lhs, vset, rename), _pp(rhs, vset, rename)
        if guard:
            return f"(rewrite {lpp} {rpp} :when ({' '.join(guard)}))"
        return f"(rewrite {lpp} {rpp})"

    def as_rule() -> str:
        body = " ".join(prems_pp)
        if is_eq:
            head = f"((union {_pp(lhs, vset, rename)} {_pp(rhs, vset, rename)}))"
        else:
            head = f"((set {_pp(concl, vset, rename)}))"
        return f"(rule ({body}) {head})"

    if not prems_pp:
        return as_rewrite()

    # variable coverage check
    head_vars = _free_vars(lhs, vset) | _free_vars(rhs, vset) if is_eq else _free_vars(concl, vset)
    if head_vars <= vars_body:
        return as_rule()
    else:
        return as_rewrite(prems_pp)

# ──────────────────────────────────────────── main entry
def convert_rare_ast(rules: Iterable["RareRule"]) -> str:
    sigs, uses_bool = _discover(rules)
    rename = _mk_rename_map(set(sigs.keys()), uses_bool)

    out = StringIO()
    out.write(_prelude(sigs, uses_bool))
    out.write(";; ---- compiled Rare rules ----\n")
    for rr in rules:
        try:
            out.write(f";; rare‑rule: {rr.name}\n")
            out.write(_encode_rule(rr, rename) + "\n")
        except ValueError as err:
            out.write(f";; skipped {rr.name}: {err}\n")
    return out.getvalue()

if __name__ == '__main__':
    import sys, pprint
    src = sys.argv[1]
    assert src, 'you need to specify the .rare file'
    with open(src, 'r+') as file:
        rules = parse_rare_rules(file.read())
        egg_log_rules = convert_rare_ast(rules)
        print(egg_log_rules)