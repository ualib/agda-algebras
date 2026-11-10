"""
File: scripts/python/certificates/unary_lattice_cert.py

Description: Generate the whole-lattice congruence certificate benchmark,
  ``src/Examples/Setoid/Certificates/Cyclic30.lagda.md``.

  A whole-lattice certificate (`LatticeCert` of
  ``Setoid.Congruences.Certificates.Schema``) lists every congruence of a
  finite algebra as a parent vector in Freese normal form, and carries a
  principal-congruence pointer for every pair of carrier indices, the meet
  and join tables, and a Freese trace for every principal and every join
  entry.

  The script has two parts, of different scope:

  + ``certificate`` computes those data, in the formats of the schema, for
    any unary algebra on ``{0, ..., n-1}`` whose operations are given by
    tables, and ``verify_certificate`` replays them; the tests run both on
    small algebras against a brute-force oracle.
  + The renderer, its template and the command line emit one module only:
    the benchmark, the integers modulo 30 with the successor map
    ``x -> x + 1``, whose eight congruences are the congruences modulo the
    eight divisors of 30.  Its prose, its names and its one-operation
    helpers are that algebra's; another algebra needs its own template.

  Per the library's certificate discipline, nothing enters the corpus on
  this script's authority: the Agda module re-checks every claim, and the
  replay in ``verify_certificate`` below is an engine-side tripwire only.

  The output is a deterministic function of the algebra and the route (the
  date in the emitted front matter is pinned below), so the committed module
  must reproduce byte for byte; ``test_unary_lattice_cert.py`` pins that.

Design Principles:

  + The certificate is computed by pure functions over tuples; the worklist
    of Freese's ``cg2`` algorithm is a fold over an immutable ``Run`` state.
  + Only ``main`` reads arguments, writes files, prints, and exits; every
    fallible step below it returns a ``Result``.

Usage:

  python3 scripts/python/certificates/unary_lattice_cert.py [--route ROUTE]
      [--out PATH] [--check]

  ``--route boolean`` (the default, and the committed module) accepts the
  certificate by ``latticeCertOK-sound``; ``--route decision`` emits the same
  module accepting it by ``from-yes (latticeCertOK? ...)`` instead, the
  comparison arm of the measurements in the checker's prose, with the
  module's prose about the check and its cost written for that route.
"""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass
from functools import reduce
from math import gcd
from pathlib import Path
from typing import (Callable, Dict, FrozenSet, Hashable, Optional, Sequence,
                    Tuple, TypeVar, Union)

# Import the shared functional utilities the way the sibling scripts do: make
# the scripts/python directory importable, then pull in the Result monad and
# the file wrappers.
_PY_ROOT = Path(__file__).resolve().parents[1]
if str(_PY_ROOT) not in sys.path:
    sys.path.insert(0, str(_PY_ROOT))

from _utils import ErrorType, PipelineError, Result  # noqa: E402
from _utils.file_ops import read_text, write_text  # noqa: E402

REPO_ROOT: Path = Path(__file__).resolve().parents[3]
DEFAULT_OUT: Path = REPO_ROOT / "src/Examples/Setoid/Certificates/Cyclic30.lagda.md"

# The emitted front matter's date is pinned so the output is byte-stable.
EMITTED_DATE: str = "2026-11-09"

ROUTES: Tuple[str, ...] = ("boolean", "decision")

S = TypeVar("S")


# ---------------------------------------------------------------------------
# The algebra and the certificate data, mirroring the Agda schema.

@dataclass(frozen=True)
class UnaryAlgebra:
    """A unary algebra on {0, ..., size-1}; tables[f][i] is f applied to i."""
    size: int
    tables: Tuple[Tuple[int, ...], ...]


# A partition as a parent vector: entry i is the representative of i's block.
Parts = Tuple[int, ...]

# A list of index pairs (seed lists and forest edges).
Pairs = Tuple[Tuple[int, int], ...]


@dataclass(frozen=True)
class Seed:
    """The merged pair is the seed at this absolute position."""
    position: int


@dataclass(frozen=True)
class Translate:
    """The merged pair is the image under operation ``op`` of the merge
    ``offset`` places before this one (0 is the immediately preceding)."""
    op: int
    offset: int


Justification = Union[Seed, Translate]


@dataclass(frozen=True)
class Merge:
    """One justified merge of a Freese trace."""
    lhs: int
    rhs: int
    why: Justification


Trace = Tuple[Merge, ...]


@dataclass(frozen=True)
class LatticeCertificate:
    """The fields of the Agda record ``LatticeCert``, in its order."""
    parts: Tuple[Parts, ...]
    bot: int
    prin: Tuple[Tuple[int, ...], ...]
    prin_traces: Tuple[Tuple[Trace, ...], ...]
    meet: Tuple[Tuple[int, ...], ...]
    join: Tuple[Tuple[int, ...], ...]
    join_traces: Tuple[Tuple[Trace, ...], ...]


def cyclic_algebra(n: int) -> UnaryAlgebra:
    """The integers modulo n with the successor map x -> x + 1."""
    return UnaryAlgebra(n, (tuple((i + 1) % n for i in range(n)),))


# The one algebra the renderer emits (see the Description above).
BENCHMARK: UnaryAlgebra = cyclic_algebra(30)


# ---------------------------------------------------------------------------
# Partitions.

def normal_form(labels: Sequence[Hashable]) -> Parts:
    """The Freese normal form of the partition whose blocks are the label
    classes: every index points at the least member of its block."""
    least: Dict[Hashable, int] = reduce(
        lambda acc, il: acc if il[1] in acc else {**acc, il[1]: il[0]},
        enumerate(labels), {})
    return tuple(least[lab] for lab in labels)


def forest_edges(pv: Parts) -> Pairs:
    """The forest edges of a parent vector, as the schema's ``forestEdges``
    lists them: each non-root index with its root, in index order."""
    return tuple((i, r) for i, r in enumerate(pv) if i != r)


def meet_partition(p: Parts, q: Parts) -> Parts:
    """The intersection of two partitions: blocks of root pairs."""
    return normal_form(tuple(zip(p, q)))


def block_count(pv: Parts) -> int:
    """The number of blocks of a partition."""
    return len(set(pv))


# ---------------------------------------------------------------------------
# Freese's cg2 run: the congruence generated by a seed list, with its trace.

@dataclass(frozen=True)
class Run:
    """The state of one run: eager root labels, the merges so far, and the
    position of the next merge whose translates are still to be taken."""
    labels: Tuple[int, ...]
    merges: Trace
    cursor: int


def union(labels: Tuple[int, ...], a: int, b: int) -> Tuple[int, ...]:
    """Merge the blocks of a and b: re-point b's root to a's (the eager
    re-pointing the Agda checker's replay also uses)."""
    ru, rv = labels[a], labels[b]
    return tuple(ru if x == rv else x for x in labels)


def record(run: Run, a: int, b: int, why: Justification) -> Run:
    """Merge a and b if they are in different blocks, recording why."""
    if run.labels[a] == run.labels[b]:
        return run
    return Run(union(run.labels, a, b), run.merges + (Merge(a, b, why),),
               run.cursor)


def translate_step(alg: UnaryAlgebra, run: Run) -> Optional[Run]:
    """Take every operation's image of the merge at the cursor, or report
    (None) that every recorded merge has been processed."""
    if run.cursor >= len(run.merges):
        return None
    source = run.merges[run.cursor]

    def image(acc: Run, f: int) -> Run:
        # the new merge, if any, lands at position len(acc.merges), so the
        # source merge lies len(acc.merges) - 1 - cursor places before it
        offset = len(acc.merges) - 1 - run.cursor
        table = alg.tables[f]
        return record(acc, table[source.lhs], table[source.rhs],
                      Translate(f, offset))

    advanced = reduce(image, range(len(alg.tables)), run)
    return Run(advanced.labels, advanced.merges, run.cursor + 1)


def fixpoint(step: Callable[[S], Optional[S]], start: S) -> S:
    """Apply step until it reports completion by returning None."""
    current, upcoming = start, step(start)
    while upcoming is not None:
        current, upcoming = upcoming, step(upcoming)
    return current


def generated(alg: UnaryAlgebra, seeds: Pairs) -> Tuple[Parts, Trace]:
    """The congruence generated by the seeds, in normal form, and the Freese
    trace of the run that generated it (seeds first, then the worklist)."""
    seeded = reduce(lambda run, sp: record(run, sp[1][0], sp[1][1], Seed(sp[0])),
                    enumerate(seeds),
                    Run(tuple(range(alg.size)), (), 0))
    final = fixpoint(lambda run: translate_step(alg, run), seeded)
    return normal_form(final.labels), final.merges


def generated_parts(alg: UnaryAlgebra, seeds: Pairs) -> Parts:
    """The congruence generated by the seeds, without its trace."""
    return generated(alg, seeds)[0]


def join_seeds(p: Parts, q: Parts) -> Pairs:
    """The seed list of a claimed join: both arguments' forest edges."""
    return forest_edges(p) + forest_edges(q)


# ---------------------------------------------------------------------------
# The whole lattice.

def join_closure(alg: UnaryAlgebra, found: FrozenSet[Parts]) -> FrozenSet[Parts]:
    """Close a set of congruences under binary joins.  Seeded with the
    diagonal and the principal congruences, this is every congruence: each
    congruence is the join of the principal congruences of its pairs."""
    joined = frozenset(generated_parts(alg, join_seeds(p, q))
                       for p in found for q in found)
    return found if joined <= found else join_closure(alg, found | joined)


def all_congruences(alg: UnaryAlgebra) -> Tuple[Parts, ...]:
    """Every congruence, finest first (the diagonal is position 0), ties
    broken by the parent vectors themselves."""
    n = alg.size
    diagonal: Parts = tuple(range(n))
    principals = frozenset(generated_parts(alg, ((i, j),))
                           for i in range(n) for j in range(n))
    closed = join_closure(alg, principals | {diagonal})
    return tuple(sorted(closed, key=lambda p: (-block_count(p), p)))


def certificate(alg: UnaryAlgebra) -> LatticeCertificate:
    """The whole-lattice certificate of a unary algebra."""
    n = alg.size
    parts = all_congruences(alg)
    position: Dict[Parts, int] = {p: k for k, p in enumerate(parts)}
    prin_runs = tuple(tuple(generated(alg, ((i, j),)) for j in range(n))
                      for i in range(n))
    join_runs = tuple(tuple(generated(alg, join_seeds(p, q)) for q in parts)
                      for p in parts)
    return LatticeCertificate(
        parts=parts,
        bot=position[tuple(range(n))],
        prin=tuple(tuple(position[r[0]] for r in row) for row in prin_runs),
        prin_traces=tuple(tuple(r[1] for r in row) for row in prin_runs),
        meet=tuple(tuple(position[meet_partition(p, q)] for q in parts)
                   for p in parts),
        join=tuple(tuple(position[r[0]] for r in row) for row in join_runs),
        join_traces=tuple(tuple(r[1] for r in row) for row in join_runs))


# ---------------------------------------------------------------------------
# Well-formedness: the constraints Agda's types put on a certificate.  In Agda
# an index is a Fin, a vector has its length in its type, and a seed position
# or an offset is a natural number, so a malformed certificate cannot even be
# written down.  Here each of those is checked first, so that the replay below
# never indexes out of range, and never lets Python's negative indices wrap a
# pointer onto another entry (parts[-1] is the last congruence).

def in_range(bound: int, x: int) -> bool:
    """x is an element of Fin bound: a non-negative index below bound."""
    return 0 <= x < bound


def is_vector(bound: int, length: int, xs: Sequence[int]) -> bool:
    """xs is a Vec (Fin bound) length."""
    return len(xs) == length and all(in_range(bound, x) for x in xs)


def is_matrix(bound: int, rows: int, cols: int,
              xss: Sequence[Sequence[int]]) -> bool:
    """xss is a Vec (Vec (Fin bound) cols) rows."""
    return len(xss) == rows and all(is_vector(bound, cols, xs) for xs in xss)


def merge_well_formed(n: int, ops: int, m: Merge) -> bool:
    """m is a Merge: both indices in Fin n, a seed position a natural number,
    and a translate's operation in Fin ops with a natural-number offset."""
    why_ok = (m.why.position >= 0 if isinstance(m.why, Seed)
              else in_range(ops, m.why.op) and m.why.offset >= 0)
    return in_range(n, m.lhs) and in_range(n, m.rhs) and why_ok


def traces_well_formed(n: int, ops: int, rows: int, cols: int,
                       tss: Sequence[Sequence[Trace]]) -> bool:
    """tss is a rows-by-cols matrix of traces of well-formed merges."""
    return len(tss) == rows and all(
        len(row) == cols and all(merge_well_formed(n, ops, m)
                                 for trace in row for m in trace)
        for row in tss)


def malformations(alg: UnaryAlgebra, cert: LatticeCertificate) -> Tuple[str, ...]:
    """The fields of the algebra and the certificate that Agda's types would
    reject (none for a well-formed pair)."""
    n, ops, m = alg.size, len(alg.tables), len(cert.parts)
    shapes: Tuple[Tuple[str, bool], ...] = (
        ("operation tables", all(is_vector(n, n, t) for t in alg.tables)),
        ("parent vectors", is_matrix(n, m, n, cert.parts)),
        ("bot", in_range(m, cert.bot)),
        ("principal pointers", is_matrix(m, n, n, cert.prin)),
        ("principal traces", traces_well_formed(n, ops, n, n, cert.prin_traces)),
        ("meet table", is_matrix(m, m, m, cert.meet)),
        ("join table", is_matrix(m, m, m, cert.join)),
        ("join traces", traces_well_formed(n, ops, m, m, cert.join_traces)))
    return tuple(name for name, ok in shapes if not ok)


# ---------------------------------------------------------------------------
# Verification pass (engine-side tripwire; the Agda checker is the authority).
# Each function mirrors one family of the fields of LatticeCertOK, and assumes
# a well-formed certificate (above).

def same_block(pv: Parts, i: int, j: int) -> bool:
    """Two indices lie in the same claimed block."""
    return pv[i] == pv[j]


def is_normal_form(pv: Parts) -> bool:
    """Idempotent and decreasing (the schema's NormalForm)."""
    return all(pv[pv[i]] == pv[i] and pv[i] <= i for i in range(len(pv)))


def edge_compatible(alg: UnaryAlgebra, pv: Parts) -> bool:
    """One root-replacement translate step per operation and argument
    (the checker's EdgeCompat, at arity one)."""
    return all(same_block(pv, t[x], t[pv[x]])
               for t in alg.tables for x in range(alg.size))


def trace_valid(alg: UnaryAlgebra, seeds: Pairs, trace: Trace) -> bool:
    """Every justification points at its seed or earlier merge, and the
    merged pair is that seed, or that merge's image (TraceValid)."""
    def ok(t: int) -> bool:
        m = trace[t]
        if isinstance(m.why, Seed):
            s = m.why.position
            return in_range(len(seeds), s) and seeds[s] == (m.lhs, m.rhs)
        # the source merge, r = t - 1 - offset, must come strictly before
        # this one; both bounds are tested before either lookup
        op, r = m.why.op, t - 1 - m.why.offset
        return (in_range(len(alg.tables), op) and in_range(t, r)
                and (m.lhs, m.rhs) == (alg.tables[op][trace[r].lhs],
                                       alg.tables[op][trace[r].rhs]))
    return all(ok(t) for t in range(len(trace)))


def replay_roots(n: int, trace: Trace) -> Tuple[int, ...]:
    """The checker's replayRoots: the trace's unions, in run order, from the
    identity, re-pointing the right root to the left."""
    return reduce(lambda labels, m: union(labels, m.lhs, m.rhs), trace,
                  tuple(range(n)))


def covers(pv: Parts, roots: Tuple[int, ...]) -> bool:
    """The replayed roots are constant along the claimed parent pointers."""
    return all(roots[pv[i]] == roots[i] for i in range(len(pv)))


def entry_ok(alg: UnaryAlgebra, pv: Parts, seeds: Pairs, trace: Trace) -> bool:
    """Respects, TraceValid and Covers for one traced entry."""
    return (all(same_block(pv, a, b) for a, b in seeds)
            and trace_valid(alg, seeds, trace)
            and covers(pv, replay_roots(alg.size, trace)))


def verify_certificate(alg: UnaryAlgebra,
                       cert: LatticeCertificate) -> Result[LatticeCertificate, PipelineError]:
    """Reject a malformed certificate, then replay the fourteen conditions of
    LatticeCertOK on the engine side.  Either failure is an err value; no
    input raises."""
    malformed = malformations(alg, cert)
    return (Result.err(PipelineError(ErrorType.VALIDATION_ERROR,
                                     "certificate is malformed: " + ", ".join(malformed)))
            if malformed else replay_conditions(alg, cert))


def replay_conditions(alg: UnaryAlgebra,
                      cert: LatticeCertificate) -> Result[LatticeCertificate, PipelineError]:
    """The fourteen conditions of LatticeCertOK, for a well-formed certificate."""
    n, parts = alg.size, cert.parts
    m = len(parts)
    pairs = [(i, j) for i in range(n) for j in range(n)]
    positions = [(k, l) for k in range(m) for l in range(m)]
    checks: Tuple[Tuple[str, bool], ...] = (
        ("normal form", all(is_normal_form(p) for p in parts)),
        ("edge compatibility", all(edge_compatible(alg, p) for p in parts)),
        ("distinct entries", len(set(parts)) == m),
        ("bot is the diagonal", parts[cert.bot] == tuple(range(n))),
        ("principal entries",
         all(entry_ok(alg, parts[cert.prin[i][j]], ((i, j),),
                      cert.prin_traces[i][j]) for i, j in pairs)),
        ("join entries",
         all(entry_ok(alg, parts[cert.join[k][l]],
                      join_seeds(parts[k], parts[l]), cert.join_traces[k][l])
             for k, l in positions)),
        ("meet entries",
         all(same_block(parts[cert.meet[k][l]], i, j)
             == (same_block(parts[k], i, j) and same_block(parts[l], i, j))
             for k, l in positions for i, j in pairs)))
    failed = tuple(name for name, ok in checks if not ok)
    return (Result.ok(cert) if not failed else
            Result.err(PipelineError(ErrorType.VALIDATION_ERROR,
                                     "certificate fails: " + ", ".join(failed))))


# ---------------------------------------------------------------------------
# Agda rendering.

def literal_names(bound: int, suffix: str) -> Callable[[int], str]:
    """The spelling of a Fin literal: Data.Fin.Patterns' 0F to 9F below ten,
    and above it a definition of this module (see literal_block)."""
    return lambda i: f"{i}F" if i < 10 else f"{i}{suffix}"


def literal_block(bound: int, suffix: str, comment: str) -> str:
    """Definitions for the literals 10 to bound-1 of Fin bound, spelled
    with #_ (a pattern synonym would expand at every use into a chain of
    suc constructors, each with an implicit length to solve)."""
    if bound <= 10:
        return ""
    defs = "\n".join(f"{i}{suffix} : Fin {bound}\n{i}{suffix} = # {i}\n"
                     for i in range(10, bound))
    return f"-- {comment}\n{defs}"


def vec(items: Sequence[str]) -> str:
    """A Vec literal on one line."""
    return " ∷ ".join(tuple(items) + ("[]",))


def vec_lines(name: str, items: Sequence[str], indent: int) -> str:
    """A Vec literal, one item per line, aligned under the first."""
    pad = " " * indent
    head = f"{name} = "
    body = f"\n{pad}∷ ".join(items)
    return f"{head}{body}\n{pad}∷ []"


def render_merge(fin: Callable[[int], str], m: Merge) -> str:
    """One merge, through the module's two helpers: sm, and tm, the image
    under the benchmark's one operation, which therefore takes none."""
    if isinstance(m.why, Seed):
        return f"sm {fin(m.lhs)} {fin(m.rhs)} {m.why.position}"
    return f"tm {fin(m.lhs)} {fin(m.rhs)} {m.why.offset}"


def render_trace(fin: Callable[[int], str], tr: Trace) -> str:
    """One trace, as a parenthesized List literal."""
    return f"({vec(tuple(render_merge(fin, m) for m in tr))})"


def render_matrix(name: str, rows: Sequence[Sequence[str]]) -> str:
    """A Vec of Vecs, one row per line."""
    return vec_lines(name, tuple(f"({vec(r)})" for r in rows), len(name) + 1)


def render_trace_matrix(name: str, fin: Callable[[int], str],
                        rows: Sequence[Sequence[Trace]]) -> str:
    """A Vec of Vecs of traces: one row per block, one trace per line."""
    pad = " " * (len(name) + 3)
    blocks = tuple(f"(" + f"\n{pad}∷ ".join(render_trace(fin, t) for t in row)
                   + f"\n{pad}∷ [])" for row in rows)
    return vec_lines(name, blocks, len(name) + 1)


@dataclass(frozen=True)
class Rendered:
    """The Agda text of each data section of the module."""
    literals: str
    tables: str
    parts: str
    prin: str
    prin_traces: str
    meet: str
    join: str
    join_traces: str


def render_data(alg: UnaryAlgebra, cert: LatticeCertificate, prefix: str) -> Rendered:
    """The data sections, as Agda text."""
    n, m = alg.size, len(cert.parts)
    fin = literal_names(n, "F")
    pos = literal_names(m, "L")
    literals = "\n".join(block for block in (
        literal_block(n, "F", f"The carrier literals from 10 on, as definitions of Fin {n}."),
        literal_block(m, "L", f"The position literals from 10 on, as definitions of Fin {m}."))
        if block)
    return Rendered(
        literals=literals,
        tables=render_matrix(f"{prefix}-tables",
                             tuple(tuple(fin(x) for x in t) for t in alg.tables)),
        parts=render_matrix(f"{prefix}-parts",
                            tuple(tuple(fin(x) for x in p) for p in cert.parts)),
        prin=render_matrix(f"{prefix}-prin",
                           tuple(tuple(pos(k) for k in row) for row in cert.prin)),
        prin_traces=render_trace_matrix(f"{prefix}-prinTr", fin, cert.prin_traces),
        meet=render_matrix(f"{prefix}-meet",
                           tuple(tuple(pos(k) for k in row) for row in cert.meet)),
        join=render_matrix(f"{prefix}-join",
                           tuple(tuple(pos(k) for k in row) for row in cert.join)),
        join_traces=render_trace_matrix(f"{prefix}-joinTr", fin, cert.join_traces))


# ---------------------------------------------------------------------------
# The emitted module.

ROUTE_IMPORTS: Dict[str, str] = {
    "boolean": "open import Relation.Binary.PropositionalEquality using ( refl )",
    "decision": "open import Relation.Nullary.Decidable using ( from-yes )",
}

ROUTE_ACCEPT: Dict[str, str] = {
    "boolean": "cyclic30-ok = latticeCertOK-sound cyclic30-cert refl",
    "decision": "cyclic30-ok = from-yes (latticeCertOK? cyclic30-cert)",
}

ROUTE_NAMES: Dict[str, str] = {
    "boolean": "latticeCertOK-sound",
    "decision": "latticeCertOK?",
}

# The command that regenerates the module, as its header states it.
ROUTE_COMMANDS: Dict[str, str] = {
    "boolean": "python3 scripts/python/certificates/unary_lattice_cert.py",
    "decision": "python3 scripts/python/certificates/unary_lattice_cert.py --route decision",
}

TEMPLATE: str = '''\
---
layout: default
file: "src/Examples/Setoid/Certificates/Cyclic30.lagda.md"
title: "Examples.Setoid.Certificates.Cyclic30 module"
date: "{date}"
author: "the agda-algebras development team"
check-cost: heavy
---

### A whole-lattice certificate for the cyclic unary algebra of order 30

This is the [Examples.Setoid.Certificates.Cyclic30][] module of the [Agda Universal Algebra Library][].

**Generated file: do not edit by hand.**  Regenerate with

    {command}

{prose}

<!--
```agda
{{-# OPTIONS --without-K --exact-split --safe #-}}

module Examples.Setoid.Certificates.Cyclic30 where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Data.Fin           using ( #_ )
open import Data.Fin.Base      using ( Fin )
open import Data.Fin.Patterns  using ( 0F ; 1F ; 2F ; 3F ; 4F ; 5F ; 6F ; 7F ; 8F ; 9F )
open import Data.List.Base     using ( [] ; _∷_ )
open import Data.Nat.Base      using ( ℕ )
open import Data.Vec.Base      using ( Vec ; [] ; _∷_ )
open import Level              using ( 0ℓ )
{route_import}

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Signatures.Unary                  using ( Sig-Unary )
open import Classical.Structures.Unary                  using ( tablesToUnaryAlgebra
                                                              ; tablesToUnaryAlgebra-FiniteAlgebra
                                                              ; Sig-Unary-Fin-FiniteSignature )
open import Setoid.Algebras.Basic                       using ( Algebra )
open import Setoid.Algebras.Finite                      using ( FiniteAlgebra )
open import Setoid.Congruences.Finite.Decidable         using ( FiniteCongruencesᵈ )
open import Setoid.Congruences.Certificates.Schema      using ( ParentVec ; seed ; translate
                                                              ; Merge ; mkMerge ; Trace
                                                              ; LatticeCert ; mkLatticeCert )
open import Setoid.Congruences.Certificates.Congruence  using ( module CertCheck )
open import Setoid.Congruences.Certificates.Lattice     using ( module LatticeCheck )
open import Setoid.Signatures.Finite                    using ( FiniteSignature )

{literals}
```
-->

#### The algebra

One unary operation, the successor; the table's only row lists `x + 1` for
each `x`.

```agda
-- The successor table of the integers modulo 30.
cyclic30-tables : Vec (Vec (Fin 30) 30) 1
{tables}

-- The algebra presented by the table.
cyclic30 : Algebra {{𝑆 = Sig-Unary (Fin 1)}} 0ℓ 0ℓ
cyclic30 = tablesToUnaryAlgebra 30 1 cyclic30-tables

-- Its carrier-finiteness and signature-finiteness data.
cyclic30-fin : FiniteAlgebra cyclic30
cyclic30-fin = tablesToUnaryAlgebra-FiniteAlgebra 30 1 cyclic30-tables

cyclic30-sig : FiniteSignature (Sig-Unary (Fin 1))
cyclic30-sig = Sig-Unary-Fin-FiniteSignature 1

open CertCheck cyclic30-fin cyclic30-sig using ( arOf )
open LatticeCheck cyclic30-fin cyclic30-sig
  using ( LatticeCertOK ; {route_name} ; certFiniteCongruencesᵈ )
```

#### The certificate

Every merge of a trace is one of two kinds: a seed pair at a position of the
seed list, or the successor's image of an earlier merge, at a backward offset
(`0` is the merge just before).  The two helpers below build them, so that a
trace reads as a list of index pairs with their justifications.

```agda
-- A merge justified by the seed at position s.
sm : Fin 30 → Fin 30 → ℕ → Merge 30 1 arOf
sm i j s = mkMerge i j (seed s)

-- A merge justified as the successor's image of the merge r places back.
tm : Fin 30 → Fin 30 → ℕ → Merge 30 1 arOf
tm i j r = mkMerge i j (translate 0F 0F (0F ∷ []) r)
```

The eight congruences, finest first, as parent vectors in Freese normal form:
position 0 is the diagonal and position 7 the total relation.

```agda
-- The congruences x ≡ y (mod d), for d = 30, 15, 10, 6, 5, 3, 2, 1.
cyclic30-parts : Vec (ParentVec 30) 8
{parts}
```

The principal congruence of each pair of carrier indices, and the trace of
the run that generated it from that one pair.

```agda
-- The position of Cg(i , j).
cyclic30-prin : Vec (Vec (Fin 8) 30) 30
{prin}

-- Its trace, with seed list (i , j) ∷ [].
cyclic30-prinTr : Vec (Vec (Trace 30 1 arOf) 30) 30
{prin_traces}
```

The meet and join tables, and the trace of each join, generated from the
forest edges of its two arguments.

```agda
-- The position of the meet of two positions.
cyclic30-meet : Vec (Vec (Fin 8) 8) 8
{meet}

-- The position of the join of two positions.
cyclic30-join : Vec (Vec (Fin 8) 8) 8
{join}

-- Its trace, with seed list the forest edges of both arguments.
cyclic30-joinTr : Vec (Vec (Trace 30 1 arOf) 8) 8
{join_traces}

-- The whole-lattice certificate.
cyclic30-cert : LatticeCert 30 1 arOf 8
cyclic30-cert = mkLatticeCert cyclic30-parts 0F cyclic30-prin cyclic30-prinTr
                              cyclic30-meet cyclic30-join cyclic30-joinTr
```

#### The check

{check_prose}

```agda
-- The fourteen conditions of the certificate, checked.
cyclic30-ok : LatticeCertOK cyclic30-cert
{route_accept}

-- The congruence lattice of the algebra: the eight listed congruences,
-- complete up to ≑ for its decidable congruences.
cyclic30-congruences : FiniteCongruencesᵈ cyclic30
cyclic30-congruences = certFiniteCongruencesᵈ cyclic30-cert cyclic30-ok
```
'''

PROSE: str = """\
The algebra is the integers modulo 30 with one unary operation, the
successor `x ↦ x + 1`.  If an equivalence relation `θ` is compatible with
the successor, then `x θ y` holds exactly when `0 θ (y - x)`, and the
residues `d` with `0 θ d` form a subgroup of the integers modulo 30.  So the
congruences are the eight relations `x ≡ y (mod d)`, one for each divisor `d`
of 30, and the congruence lattice is the Boolean lattice of the divisors of
30, ordered by reverse divisibility.

The certificate below (`LatticeCert`{.AgdaRecord} of
[Setoid.Congruences.Certificates.Schema][]) lists the eight congruences, a
principal congruence and its Freese trace for each of the 900 pairs of
carrier indices, and the meet and join tables, each join with its trace.
[Setoid.Congruences.Certificates.Lattice][] checks all of it, and the
certified lattice comes out as a `FiniteCongruencesᵈ`{.AgdaRecord} instance:
the eight entries are decidable congruences, and every decidable congruence
of the algebra is `≑` to one of them.

The module is also the library's benchmark for the checker, a certificate
large enough that the route by which it is accepted matters: each of the
three meet conditions alone is a sweep of `8² · 30² = 57 600` cases, and the
principal traces hold 22 950 merges."""

# The module's check cost, as measured for each route (the checker's prose
# has the table: 30.6 s and 1.40 GB, and 30.8 s and 1.46 GB).
ROUTE_COSTS: Dict[str, str] = {
    "boolean": """\
**Check cost**.  Checked alone from no interface under the build's RTS
options, on a performance core, the module takes about 31 seconds and 1.4 GB
of maximum residency (9 seconds and 0.7 GB of which are its data), so the
front matter above says `check-cost: heavy` and no barrel imports it.  `make
check` checks it.""",
    "decision": """\
**Check cost**.  Checked alone from no interface under the build's RTS
options, on a performance core, this route's module takes about 31 seconds and
1.5 GB of maximum residency (9 seconds and 0.7 GB of which are its data), so
the front matter above says `check-cost: heavy`.""",
}

# How the certificate is accepted, for each route.
ROUTE_CHECKS: Dict[str, str] = {
    "boolean": """\
The certificate is accepted by `latticeCertOK-sound`{.AgdaFunction} applied to
`refl`: the type checker evaluates the Boolean `latticeCertOKᵇ`{.AgdaFunction}
of the certificate once, compares it with `true`, and the soundness lemma reads
the fourteen conditions back.  The checker's prose says why a concrete
certificate takes this route, with the measurements made on this module.""",
    "decision": """\
The certificate is accepted by `from-yes`{.AgdaFunction} applied to the
decision `latticeCertOK?`{.AgdaFunction} of the certificate.  The decision is
derived from the Boolean `latticeCertOKᵇ`{.AgdaFunction} by its soundness and
completeness lemmas, so the type checker evaluates the Boolean once, and
`from-yes`{.AgdaFunction} returns the proof the soundness lemma builds.  This
is the comparison arm of the measurements in the checker's prose; the
committed module is accepted by `latticeCertOK-sound`{.AgdaFunction} applied
to `refl`.""",
}


def emitted_module(cert: LatticeCertificate, route: str) -> str:
    """The module text for the benchmark's certificate, accepted by the route."""
    data = render_data(BENCHMARK, cert, "cyclic30")
    return TEMPLATE.format(
        date=EMITTED_DATE, command=ROUTE_COMMANDS[route],
        prose=PROSE + "\n\n" + ROUTE_COSTS[route],
        check_prose=ROUTE_CHECKS[route], route_import=ROUTE_IMPORTS[route],
        route_name=ROUTE_NAMES[route], route_accept=ROUTE_ACCEPT[route],
        literals=data.literals,
        tables=data.tables, parts=data.parts, prin=data.prin,
        prin_traces=data.prin_traces, meet=data.meet, join=data.join,
        join_traces=data.join_traces)


def generate(route: str = "boolean") -> Result[str, PipelineError]:
    """Build, verify, and render the benchmark module."""
    return (verify_certificate(BENCHMARK, certificate(BENCHMARK))
            .map(lambda cert: emitted_module(cert, route)))


# ---------------------------------------------------------------------------
# CLI shell.

def compare(path: Path, text: str) -> Result[Path, PipelineError]:
    """Succeed when the file at path holds exactly text."""
    return read_text(path).and_then(
        lambda committed: Result.ok(path) if committed == text else
        Result.err(PipelineError(ErrorType.VALIDATION_ERROR,
                                 f"stale: {path} does not match the generator output")))


def write(path: Path, text: str) -> Result[Path, PipelineError]:
    """Write text to path, answering the path (write_text answers None)."""
    return write_text(path, text).map(lambda _: path)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--route", choices=ROUTES, default="boolean")
    parser.add_argument("--check", action="store_true",
                        help="compare against the file at --out instead of writing")
    args = parser.parse_args()
    act = compare if args.check else write
    outcome = generate(args.route).and_then(lambda text: act(args.out, text))
    if outcome.is_err:
        print(str(outcome.unwrap_err()), file=sys.stderr)
        return 1
    print(f"{'ok' if args.check else 'wrote'}: {outcome.unwrap()}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
