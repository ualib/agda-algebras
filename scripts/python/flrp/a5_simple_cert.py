"""
File: scripts/python/flrp/a5_simple_cert.py

Description: Generate the A5 simplicity-certificate tables module.

  Constructs the alternating group A5 as the 60 even permutations of five
  points in lexicographic order (so index 0 is the identity), and emits
  ``src/Examples/Classical/Groups/AlternatingGroup5/Tables.lagda.md``:

  + the 60 x 60 Cayley table, the inverse vector, and the 60 x 5 action
    table (each element's permutation of the five points), which let the
    Agda side discharge the group laws by decision procedures, with
    associativity through the faithful action (``Overture.Cayley``);
  + the simplicity certificate, in the closure-term language of
    ``Classical.Structures.Group.NormalClosure``: for each of the 59
    non-identity elements, terms expressing the two generators as products
    of conjugates of that element and its inverse, plus one shared table
    expressing all 60 elements as words in the two generators.

  Per the certificate discipline (roadmap section 6), nothing enters the
  corpus on this script's authority: the Agda module replays every claim
  by decidable equality over the finite carrier, and the script's own
  verification pass is an engine-side tripwire only.

  The output is a deterministic function of nothing (the date in the
  emitted header is pinned below), so the committed module must reproduce
  byte for byte; ``test_a5_simple_cert.py`` pins that.

Usage:

  python3 scripts/python/flrp/a5_simple_cert.py [--out PATH] [--check]
"""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass
from itertools import permutations
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple, Union

REPO_ROOT = Path(__file__).resolve().parents[3]
DEFAULT_OUT = REPO_ROOT / "src/Examples/Classical/Groups/AlternatingGroup5/Tables.lagda.md"

# The emitted header's date is pinned so the output is byte-stable.
EMITTED_DATE = "2026-08-30"

N_POINTS = 5
ORDER = 60

Perm = Tuple[int, ...]


# ---------------------------------------------------------------------------
# The group A5 on five points, elements in lexicographic order.

def is_even(p: Perm) -> bool:
    """Parity of a permutation by inversion count."""
    return sum(1 for i in range(len(p)) for j in range(i + 1, len(p))
               if p[i] > p[j]) % 2 == 0


def a5_elements() -> Tuple[Perm, ...]:
    """The even permutations of five points, lexicographically sorted;
    the identity is first, so index 0 is the group identity."""
    return tuple(p for p in permutations(range(N_POINTS)) if is_even(p))


def compose(p: Perm, q: Perm) -> Perm:
    """p after q: (p . q)(i) = p(q(i)), matching the Agda action check
    act (a * b) q = act a (act b q)."""
    return tuple(p[q[i]] for i in range(len(q)))


def invert(p: Perm) -> Perm:
    """The inverse permutation."""
    out = [0] * len(p)
    for i, v in enumerate(p):
        out[v] = i
    return tuple(out)


@dataclass(frozen=True)
class GroupTables:
    """A5 in table form: Cayley table, inverse vector, and the action of
    each element on the five points (its own one-line notation)."""

    mul: Tuple[Tuple[int, ...], ...]
    inv: Tuple[int, ...]
    act: Tuple[Perm, ...]
    gen_s: int   # the 5-cycle (0 1 2 3 4)
    gen_t: int   # the 3-cycle (0 1 2)


def build_tables() -> GroupTables:
    """A5's tables from the canonical element order."""
    elems = a5_elements()
    index: Dict[Perm, int] = {p: i for i, p in enumerate(elems)}
    mul = tuple(tuple(index[compose(a, b)] for b in elems) for a in elems)
    inv = tuple(index[invert(a)] for a in elems)
    return GroupTables(
        mul=mul, inv=inv, act=elems,
        gen_s=index[(1, 2, 3, 4, 0)], gen_t=index[(1, 2, 0, 3, 4)])


# ---------------------------------------------------------------------------
# Closure terms (the Agda ClosureTerm language, mirrored).

@dataclass(frozen=True)
class One:
    pass


@dataclass(frozen=True)
class Seed:
    index: int


@dataclass(frozen=True)
class Inv:
    arg: "Term"


@dataclass(frozen=True)
class Mul:
    left: "Term"
    right: "Term"


@dataclass(frozen=True)
class Cnj:
    by: int
    arg: "Term"


Term = Union[One, Seed, Inv, Mul, Cnj]


def eval_term(t: Term, sigma: Sequence[int], g: GroupTables) -> int:
    """Evaluate a term at a seed assignment, mirroring the Agda semantics
    (cnj g e is g * e * g^-1)."""
    if isinstance(t, One):
        return 0
    if isinstance(t, Seed):
        return sigma[t.index]
    if isinstance(t, Inv):
        return g.inv[eval_term(t.arg, sigma, g)]
    if isinstance(t, Mul):
        return g.mul[eval_term(t.left, sigma, g)][eval_term(t.right, sigma, g)]
    return g.mul[g.mul[t.by][eval_term(t.arg, sigma, g)]][g.inv[t.by]]


def mul_fold(factors: Sequence[Term]) -> Term:
    """The left-associated product of a nonempty factor list, or `one`."""
    if not factors:
        return One()
    term = factors[0]
    for f in factors[1:]:
        term = Mul(term, f)
    return term


# ---------------------------------------------------------------------------
# The certificate words.

def bfs_words(edges: Sequence[Tuple[int, Term]], g: GroupTables) -> List[Optional[List[Term]]]:
    """Shortest factor lists from the identity to every element, where each
    step multiplies on the right by an edge element (its term recorded).
    Unreached elements stay None."""
    words: List[Optional[List[Term]]] = [None] * ORDER
    words[0] = []
    frontier = [0]
    while frontier:
        nxt: List[int] = []
        for e in frontier:
            base = words[e]
            assert base is not None
            for elem, term in edges:
                target = g.mul[e][elem]
                if words[target] is None:
                    words[target] = base + [term]
                    nxt.append(target)
        frontier = nxt
    return words


def generator_words(g: GroupTables) -> List[Term]:
    """For every element, a closure term over two seeds (the generators s
    and t) evaluating to it.  Full coverage is exactly the statement that
    s and t generate A5, asserted here and replayed in Agda."""
    edges: List[Tuple[int, Term]] = [
        (g.gen_s, Seed(0)), (g.inv[g.gen_s], Inv(Seed(0))),
        (g.gen_t, Seed(1)), (g.inv[g.gen_t], Inv(Seed(1)))]
    words = bfs_words(edges, g)
    assert all(w is not None for w in words), "s and t do not generate A5"
    terms = [mul_fold(w) for w in words if w is not None]
    for y, term in enumerate(terms):
        assert eval_term(term, [g.gen_s, g.gen_t], g) == y
    return terms


def seed_words(x: int, g: GroupTables) -> Tuple[Term, Term]:
    """For a non-identity element x, terms over one seed (x itself)
    expressing the generators s and t as products of conjugates of x and
    of its inverse.  Existence for every x is exactly simplicity of A5 by
    the normal-closure route, asserted here and replayed in Agda."""
    factors: Dict[int, Term] = {}
    for conjugator in range(ORDER):
        for base, term in ((x, Seed(0)), (g.inv[x], Inv(Seed(0)))):
            value = g.mul[g.mul[conjugator][base]][g.inv[conjugator]]
            if value not in factors:
                factors[value] = Cnj(conjugator, term)
    words = bfs_words(sorted(factors.items()), g)
    ws, wt = words[g.gen_s], words[g.gen_t]
    assert ws is not None and wt is not None, f"normal closure of {x} misses a generator"
    term_s, term_t = mul_fold(ws), mul_fold(wt)
    assert eval_term(term_s, [x], g) == g.gen_s
    assert eval_term(term_t, [x], g) == g.gen_t
    return term_s, term_t


# ---------------------------------------------------------------------------
# Verification pass (engine-side tripwire; the Agda checker is the authority).

def verify_group(g: GroupTables) -> None:
    """The five group laws plus the action facts the Agda side decides."""
    for a in range(ORDER):
        assert g.mul[0][a] == a and g.mul[a][0] == a
        assert g.mul[g.inv[a]][a] == 0 and g.mul[a][g.inv[a]] == 0
        for b in range(ORDER):
            assert compose(g.act[a], g.act[b]) == g.act[g.mul[a][b]]
    assert len({g.act[a] for a in range(ORDER)}) == ORDER  # faithful
    # Associativity follows from the two action facts, as in the Agda proof;
    # check it directly anyway (cheap in Python, cubic in the order).
    for a in range(ORDER):
        for b in range(ORDER):
            ab = g.mul[a][b]
            for c in range(ORDER):
                assert g.mul[ab][c] == g.mul[a][g.mul[b][c]]


# ---------------------------------------------------------------------------
# Agda rendering.

def fin(i: int) -> str:
    """A Fin literal; past 9F the emitted module declares its own pattern
    synonyms in the Data.Fin.Patterns style."""
    return f"{i}F"


def render(t: Term) -> str:
    """A closure-term literal, parenthesized for argument position."""
    if isinstance(t, One):
        return "one"
    if isinstance(t, Seed):
        return f"(seed {fin(t.index)})"
    if isinstance(t, Inv):
        return f"(inv {render(t.arg)})"
    if isinstance(t, Mul):
        return f"(mul {render(t.left)} {render(t.right)})"
    return f"(cnj {fin(t.by)} {render(t.arg)})"


def render_top(t: Term) -> str:
    """A closure-term literal without the outer parentheses."""
    inner = render(t)
    return inner[1:-1] if inner.startswith("(") else inner


def vec_lines(prefix: str, items: Sequence[str]) -> List[str]:
    """`prefix item0 ∷ item1 ∷ … ∷ []` with ∷ aligned under the '=' of the
    prefix, the repository's Cayley-table layout."""
    pad = " " * (len(prefix) - 2)
    out = [prefix + items[0]]
    out.extend(pad + "∷ " + item for item in items[1:])
    out.append(pad + "∷ []")
    return out


def fin_row(xs: Sequence[int]) -> str:
    return "(" + " ∷ ".join(fin(x) for x in xs) + " ∷ [])"


def emitted_module(g: GroupTables, gen_terms: Sequence[Term],
                   seeds_s: Sequence[Term], seeds_t: Sequence[Term]) -> str:
    """The full text of the Tables module."""
    synonyms = "\n".join(f"pattern {i}F = suc {i - 1}F" for i in range(10, ORDER))
    mul_block = "\n".join(vec_lines("a5-mul-table = ", [fin_row(row) for row in g.mul]))
    inv_block = "\n".join(vec_lines("a5-inv-vec = ", [fin(v) for v in g.inv]))
    act_block = "\n".join(vec_lines("a5-act-table = ", [fin_row(row) for row in g.act]))
    gen_block = "\n".join(vec_lines("a5-gen-words = ", [render_top(t) for t in gen_terms]))
    seeds_s_block = "\n".join(vec_lines("a5-seed-words-s = ", [render_top(t) for t in seeds_s]))
    seeds_t_block = "\n".join(vec_lines("a5-seed-words-t = ", [render_top(t) for t in seeds_t]))

    return f'''---
layout: default
file: "src/Examples/Classical/Groups/AlternatingGroup5/Tables.lagda.md"
title: "Examples.Classical.Groups.AlternatingGroup5.Tables module"
date: "{EMITTED_DATE}"
author: "the agda-algebras development team"
---

### Generated tables for the alternating group `A₅`

This is the [Examples.Classical.Groups.AlternatingGroup5.Tables][] module of the [Agda Universal Algebra Library][].

**Generated file: do not edit by hand.**  Regenerate with

    python3 scripts/python/flrp/a5_simple_cert.py

The module carries the raw data for the certified `A₅` of
[Examples.Classical.Groups.AlternatingGroup5][]: the Cayley table, inverse
vector, and point action of the 60 even permutations of five points in
lexicographic order (index 0 is the identity), the indices of the generators
`s = (0 1 2 3 4)` and `t = (0 1 2)`, and the simplicity certificate in the
closure-term language of [Classical.Structures.Group.NormalClosure][]: for the
`i`-th non-identity element `x`, `a5-seed-words-s`{{.AgdaFunction}} and
`a5-seed-words-t`{{.AgdaFunction}} express the generators as products of
conjugates of `x` and of its inverse, and `a5-gen-words`{{.AgdaFunction}}
expresses every element as a word in the generators.  Every claim in this data
is replayed by decision procedures in the consuming module; nothing rests on
the generator's authority.

<!--
```agda
{{-# OPTIONS --cubical-compatible --exact-split --safe #-}}

module Examples.Classical.Groups.AlternatingGroup5.Tables where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Data.Fin.Base      using ( Fin ; suc )
open import Data.Fin.Patterns  using ( 0F ; 1F ; 2F ; 3F ; 4F ; 5F ; 6F ; 7F ; 8F ; 9F )
open import Data.Vec.Base      using ( Vec ; _∷_ ; [] )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Cayley                           using ( Table )
open import Classical.Structures.Group.NormalClosure  using ( ClosureTerm ; one
                                                            ; seed ; inv ; mul ; cnj )

-- Data.Fin.Patterns stops at 9F; the larger literals this module needs are
-- pattern synonyms in the same style.
{synonyms}
```
-->

#### The Cayley table, inverse vector, and point action

```agda
-- The A₅ multiplication table on the lexicographic even-permutation encoding.
a5-mul-table : Table 60
{mul_block}

-- The inverse of each element.
a5-inv-vec : Vec (Fin 60) 60
{inv_block}

-- The action on the five points: row a is the one-line notation of element a.
a5-act-table : Vec (Vec (Fin 5) 5) 60
{act_block}
```

#### The generators

```agda
-- The 5-cycle (0 1 2 3 4).
a5-gen-s : Fin 60
a5-gen-s = {fin(g.gen_s)}

-- The 3-cycle (0 1 2).
a5-gen-t : Fin 60
a5-gen-t = {fin(g.gen_t)}
```

#### The simplicity certificate

```agda
-- Every element as a word in the generators: seed 0 is s, seed 1 is t.
a5-gen-words : Vec (ClosureTerm (Fin 60) 2) 60
{gen_block}

-- For the i-th non-identity element x, the generator s as a product of
-- conjugates of x and of its inverse (the one seed is x).
a5-seed-words-s : Vec (ClosureTerm (Fin 60) 1) 59
{seeds_s_block}

-- The same for the generator t.
a5-seed-words-t : Vec (ClosureTerm (Fin 60) 1) 59
{seeds_t_block}
```
'''


# ---------------------------------------------------------------------------
# CLI shell.

def generate() -> str:
    """Build, verify, and render the module text."""
    g = build_tables()
    verify_group(g)
    gen_terms = generator_words(g)
    seed_pairs = [seed_words(x, g) for x in range(1, ORDER)]
    return emitted_module(g, gen_terms,
                          [s for s, _ in seed_pairs], [t for _, t in seed_pairs])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--check", action="store_true",
                        help="compare against the committed module instead of writing")
    args = parser.parse_args()
    text = generate()
    if args.check:
        if not args.out.exists() or args.out.read_text() != text:
            print(f"stale: {args.out} does not match the generator output",
                  file=sys.stderr)
            return 1
        print(f"ok: {args.out} is up to date")
        return 0
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(text)
    print(f"wrote {args.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
