"""Sublattice-of-Eq(n) search and Snow closure tests.

The search side of the FLRP computational campaign (issue #486), converse in
direction to ``lattice.py``: where the emitter pipeline starts from a finite
algebra and computes its congruence lattice, this module starts from a target
lattice ``L`` and hunts for concrete representations —

+ every sublattice of ``Eq(n)`` isomorphic to ``L`` whose bounds are the
  diagonal and the total relation (a congruence lattice always has these
  bounds, so nothing else can ever be one);
+ the classification of the copies up to relabeling of the ``n`` points;
+ for each class, the Snow closure test: the monoid ``M`` of *all* unary maps
  preserving the copy's nontrivial relations, and the lattice ``Inv(M)`` of
  relations preserved by every member of ``M``.  Since the congruence lattice
  of an arbitrary algebra is determined by its unary polynomials, the copy is
  the congruence lattice of an algebra on those ``n`` points iff ``Inv(M)``
  is exactly the copy — and then the unary algebra ``⟨X, M⟩`` itself is a
  witness, ready to flow through ``cg2.py``/``emit_agda.py`` into an
  Agda-checked certificate.

Everything here is engine-side and untrusted, per roadmap § 6: a positive
find becomes a claim file for the certificate pipeline, and only the Agda
checker's acceptance counts.  Negative sweeps are recorded as JSON reports.

Provenance: generalizes the 2026-07-22 ``L7`` session (issue #484), which
found the minimal ``Eq(6)`` representation of ``L7`` and proved by these
closure tests that no algebra on at most 7 points has ``Con ≅ L7``.

Design constraints, matching ``cg2.py``:

+ partitions are parent vectors in Freese normal form (every index points
  directly at the least element of its block), the shared vocabulary of the
  whole pipeline;
+ deterministic — partitions are enumerated in a fixed order, copies are
  reported sorted, class representatives are first-found among sorted copies
  — so the same input always yields byte-identical reports.
"""

from __future__ import annotations

import json
import sys
from dataclasses import dataclass
from itertools import permutations
from pathlib import Path
from typing import Dict, FrozenSet, Iterator, List, Optional, Sequence, Set, Tuple

from cg2 import (Algebra, CertificateError, Operation, UnionFind,
                 forest_edges)
from lattice import TargetLattice, partition_meet, validate_lattice

Part = Tuple[int, ...]          # normal-form parent vector
Copy = Tuple[int, ...]          # partition index per target-lattice element


# ---------------------------------------------------------------------------
# Partitions of range(n) as normal-form parent vectors

def all_partitions(n: int) -> Tuple[Part, ...]:
    """Every partition of ``range(n)``, in the lexicographic order of their
    restricted-growth strings, each converted to a normal-form parent
    vector.  The order is the enumeration contract of the whole module."""

    def extend(prefix: List[int], blocks: int) -> Iterator[Tuple[int, ...]]:
        if len(prefix) == n:
            yield tuple(prefix)
            return
        for label in range(blocks + 1):
            prefix.append(label)
            yield from extend(prefix, blocks + (1 if label == blocks else 0))
            prefix.pop()

    def to_parent(rgs: Tuple[int, ...]) -> Part:
        leader: Dict[int, int] = {}
        for i, label in enumerate(rgs):
            leader.setdefault(label, i)
        return tuple(leader[label] for label in rgs)

    return tuple(to_parent(rgs) for rgs in extend([], 0))


def partition_join(p: Sequence[int], q: Sequence[int]) -> Part:
    """The join of two partitions in Eq(n): the transitive closure of the
    union, via union-find over both arguments' forest edges."""
    uf = UnionFind(len(p))
    for i, root in forest_edges(p) + forest_edges(q):
        uf.union(i, root)
    return uf.normal_form(len(p))


def relabel(p: Sequence[int], perm: Sequence[int]) -> Part:
    """The image of a partition under the point permutation ``i ↦ perm[i]``,
    renormalized to a parent vector."""
    uf = UnionFind(len(p))
    for i, root in forest_edges(p):
        uf.union(perm[i], perm[root])
    return uf.normal_form(len(p))


# ---------------------------------------------------------------------------
# The target lattice: bounds, heights, tables from an order relation

def tables_from_leq(name: str, leq: Sequence[Sequence[bool]]) -> TargetLattice:
    """Build a ``TargetLattice`` from a reflexive order matrix, computing
    each meet and join as the unique extremal common bound; raises
    ``CertificateError`` if some pair lacks one (not a lattice)."""
    m = len(leq)

    def extremal(x: int, y: int, lower: bool) -> int:
        bounds = [z for z in range(m)
                  if (leq[z][x] and leq[z][y] if lower else leq[x][z] and leq[y][z])]
        best = [z for z in bounds
                if all(leq[w][z] if lower else leq[z][w] for w in bounds)]
        if len(best) != 1:
            kind = "meet" if lower else "join"
            raise CertificateError(f"lattice {name}: no unique {kind} for ({x}, {y})")
        return best[0]

    return TargetLattice(
        name=name, size=m,
        meet=tuple(tuple(extremal(x, y, True) for y in range(m)) for x in range(m)),
        join=tuple(tuple(extremal(x, y, False) for y in range(m)) for x in range(m)))


def validate_target(lat: TargetLattice) -> Tuple[int, int]:
    """Check the tables are a bounded lattice of size ≥ 2 (commutative,
    idempotent, absorbing, associative) and return (bottom, top)."""
    validate_lattice(lat)
    m, meet, join = lat.size, lat.meet, lat.join
    if m < 2:
        raise CertificateError(f"lattice {lat.name}: need at least two elements")
    for table, other, kind in ((meet, join, "meet"), (join, meet, "join")):
        for x in range(m):
            if table[x][x] != x:
                raise CertificateError(f"lattice {lat.name}: {kind} not idempotent")
            for y in range(m):
                if table[x][y] != table[y][x]:
                    raise CertificateError(f"lattice {lat.name}: {kind} not commutative")
                if other[x][table[x][y]] != x:
                    raise CertificateError(f"lattice {lat.name}: absorption fails")
                for z in range(m):
                    if table[table[x][y]][z] != table[x][table[y][z]]:
                        raise CertificateError(f"lattice {lat.name}: {kind} not associative")
    bots = [b for b in range(m) if all(meet[b][x] == b for x in range(m))]
    tops = [t for t in range(m) if all(join[t][x] == t for x in range(m))]
    if len(bots) != 1 or len(tops) != 1:
        raise CertificateError(f"lattice {lat.name}: bounds are missing")
    return bots[0], tops[0]


def heights(lat: TargetLattice, bot: int) -> Tuple[int, ...]:
    """The height of every element (longest chain up from the bottom)."""
    below = {x: [y for y in range(lat.size) if lat.meet[x][y] == y and y != x]
             for x in range(lat.size)}
    result: Dict[int, int] = {bot: 0}

    def height(x: int) -> int:
        if x not in result:
            result[x] = 1 + max(height(y) for y in below[x])
        return result[x]

    return tuple(height(x) for x in range(lat.size))


# ---------------------------------------------------------------------------
# The embedding search

@dataclass(frozen=True)
class Step:
    """One backtracking step: assign lattice element ``element``; its value
    is forced to ``op[left][right]`` when ``forced`` is set; then every
    listed constraint ``(u, v, result, is_meet)`` — scheduled here because
    this step completes its participants — must hold in the Eq(n) tables."""

    element: int
    forced: Optional[Tuple[str, int, int]]
    checks: Tuple[Tuple[int, int, int, bool], ...]


def assignment_plan(lat: TargetLattice, bot: int, top: int) -> Tuple[Step, ...]:
    """The deterministic backtracking schedule: bounds are preassigned, free
    elements follow in order of (height, index), every meet/join constraint
    of the target is checked at the first step where all three participants
    are assigned, and an element that is the meet or join of two earlier
    ones is forced rather than enumerated."""
    hs = heights(lat, bot)
    free = sorted((x for x in range(lat.size) if x not in (bot, top)),
                  key=lambda x: (hs[x], x))
    when = {bot: -1, top: -1, **{x: s for s, x in enumerate(free)}}

    def schedule(u: int, v: int, result: int) -> int:
        return max(when[u], when[v], when[result])

    steps: List[Step] = []
    for s, z in enumerate(free):
        checks: List[Tuple[int, int, int, bool]] = []
        for u in range(lat.size):
            for v in range(u, lat.size):
                for table, is_meet in ((lat.meet, True), (lat.join, False)):
                    if schedule(u, v, table[u][v]) == s:
                        checks.append((u, v, table[u][v], is_meet))
        forced = next(
            (("meet" if is_meet else "join", u, v)
             for u, v, result, is_meet in checks
             if result == z and when[u] < s and when[v] < s),
            None)
        steps.append(Step(element=z, forced=forced, checks=tuple(checks)))
    return tuple(steps)


class EqTables:
    """Meet and join tables of Eq(n) over the canonical partition list."""

    def __init__(self, n: int) -> None:
        self.n = n
        self.parts = all_partitions(n)
        self.index: Dict[Part, int] = {p: i for i, p in enumerate(self.parts)}
        self.bot = self.index[tuple(range(n))]
        self.top = self.index[(0,) * n]
        size = len(self.parts)
        self.meet: List[List[int]] = [[0] * size for _ in range(size)]
        self.join: List[List[int]] = [[0] * size for _ in range(size)]
        for i in range(size):
            for j in range(i, size):
                m = self.index[partition_meet(self.parts[i], self.parts[j])]
                v = self.index[partition_join(self.parts[i], self.parts[j])]
                self.meet[i][j] = self.meet[j][i] = m
                self.join[i][j] = self.join[j][i] = v


def sublattice_copies(lat: TargetLattice, eq: EqTables) -> List[Copy]:
    """Every embedding of the target into Eq(n) sending bottom to the
    diagonal and top to the total relation, as tuples of partition indices
    per lattice element, in lexicographic order of those tuples."""
    bot, top = validate_target(lat)
    plan = assignment_plan(lat, bot, top)
    phi: List[int] = [-1] * lat.size
    phi[bot], phi[top] = eq.bot, eq.top
    used: Set[int] = {eq.bot, eq.top}
    found: List[Copy] = []

    def ok(step: Step) -> bool:
        return all((eq.meet if is_meet else eq.join)[phi[u]][phi[v]] == phi[r]
                   for u, v, r, is_meet in step.checks)

    def extend(s: int) -> None:
        if s == len(plan):
            found.append(tuple(phi))
            return
        step = plan[s]
        if step.forced is not None:
            kind, u, v = step.forced
            candidates: Sequence[int] = \
                ((eq.meet if kind == "meet" else eq.join)[phi[u]][phi[v]],)
        else:
            candidates = range(len(eq.parts))
        for value in candidates:
            if value in used:
                continue
            phi[step.element] = value
            used.add(value)
            if ok(step):
                extend(s + 1)
            used.remove(value)
            phi[step.element] = -1

    extend(0)
    return sorted(found)


# ---------------------------------------------------------------------------
# Classification up to relabeling of the points

@dataclass(frozen=True)
class ClassReport:
    """One relabeling class of copies, with its Snow closure verdict."""

    representative: Tuple[Part, ...]    # partitions, per lattice element
    orbit_size: int
    group_order: int                    # relation-preserving bijections
    monoid_size: int                    # all relation-preserving unary maps
    proper_maps: int                    # non-bijective, non-constant members
    invariants: int                     # |Inv(M)| over all of Eq(n)
    closed: bool                        # Inv(M) is exactly the copy


def classify(copies: Sequence[Copy], eq: EqTables) -> List[Tuple[Copy, int]]:
    """Group the copies into orbits under relabeling of the points.

    Copies are identified by their *unordered* relation sets (frozensets of
    partition indices): two embeddings differing only by an automorphism of
    the target lattice present the same sublattice of Eq(n), and the closure
    test of ``closure_report`` depends only on that relation set.  So this
    classifies sublattices rather than embeddings — orbit sizes count
    distinct relation sets, and the copy census may exceed the class-size
    total when the target has automorphisms.  Returns one (first-found
    representative, orbit size) per class, in the order the representatives
    occur in the sorted copy list."""
    seen: Dict[FrozenSet[int], int] = {}
    classes: List[Tuple[Copy, int]] = []
    for copy in copies:
        key = frozenset(copy)
        if key in seen:
            continue
        images = {frozenset(eq.index[relabel(eq.parts[i], perm)] for i in copy)
                  for perm in permutations(range(eq.n))}
        for image in images:
            seen[image] = len(classes)
        classes.append((copy, len(images)))
    if sum(size for _, size in classes) != len({frozenset(c) for c in copies}):
        raise CertificateError("orbit sweep lost copies (relabeling bug)")
    return classes


# ---------------------------------------------------------------------------
# The Snow closure test

def preserving_maps(relations: Sequence[Part], n: int) -> List[Tuple[int, ...]]:
    """All unary maps ``f`` on ``range(n)`` with ``x ~ y ⇒ f(x) ~ f(y)`` for
    every listed relation, by backtracking over ``f(0), …, f(n−1)`` with the
    constraints that mention only settled values checked as they close."""
    settled: List[List[Tuple[int, Part]]] = [[] for _ in range(n)]
    for r in relations:
        for y in range(n):
            for x in range(y):
                if r[x] == r[y]:
                    settled[y].append((x, r))
    out: List[Tuple[int, ...]] = []
    f: List[int] = [0] * n

    def extend(y: int) -> None:
        if y == n:
            out.append(tuple(f))
            return
        for value in range(n):
            f[y] = value
            if all(r[f[x]] == r[value] for x, r in settled[y]):
                extend(y + 1)

    extend(0)
    return out


def invariant_partitions(maps: Sequence[Tuple[int, ...]],
                         eq: EqTables) -> List[Part]:
    """The partitions preserved by every listed map — ``Inv(M)`` — filtered
    progressively; the identity and the constants preserve everything and
    are skipped."""
    identity = tuple(range(eq.n))
    candidates: List[Part] = list(eq.parts)
    for f in maps:
        if f == identity or len(set(f)) == 1:
            continue
        candidates = [p for p in candidates
                      if all(p[f[i]] == p[f[root]] for i, root in forest_edges(p))]
    return candidates


def closure_report(copy: Copy, orbit_size: int, eq: EqTables) -> ClassReport:
    """The Snow closure verdict for one copy: enumerate the preserving
    monoid of its nontrivial relations, compute ``Inv(M)``, and compare."""
    parts = tuple(eq.parts[i] for i in copy)
    relations = [p for p in parts if p not in (eq.parts[eq.bot], eq.parts[eq.top])]
    monoid = preserving_maps(relations, eq.n)
    bijections = sum(1 for f in monoid if len(set(f)) == eq.n)
    constants = sum(1 for f in monoid if len(set(f)) == 1)
    invariants = invariant_partitions(monoid, eq)
    return ClassReport(
        representative=parts,
        orbit_size=orbit_size,
        group_order=bijections,
        monoid_size=len(monoid),
        proper_maps=len(monoid) - bijections - constants,
        invariants=len(invariants),
        closed=set(invariants) == set(parts))


# ---------------------------------------------------------------------------
# From a closed class to the certificate pipeline

def closed_class_algebra(name: str, report: ClassReport, n: int) -> Algebra:
    """The unary algebra ``⟨X, M⟩`` witnessing a closed class, with the
    identity and the constants dropped (they preserve everything, so the
    congruence lattice is unchanged) and the remaining maps in sorted order."""
    if not report.closed:
        raise CertificateError(f"{name}: class is not closed, no witness algebra")
    relations = [p for p in report.representative
                 if p != tuple(range(n)) and p != tuple(0 for _ in range(n))]
    identity = tuple(range(n))
    maps = [f for f in preserving_maps(relations, n)
            if f != identity and len(set(f)) > 1]
    return Algebra(
        name=f"{name} closure witness on {n} points",
        card=n,
        operations=tuple(Operation(f"u{k}", 1, list(f))
                         for k, f in enumerate(sorted(maps))))


def claim_input(module_name: str, date: str, alg: Algebra,
                lat: TargetLattice) -> str:
    """A ``flrp-cert-input v1`` claim file (as JSON text) asserting that the
    witness algebra's congruence lattice is the target — ready for
    ``emit_agda.py``."""
    payload = {
        "format": "flrp-cert-input v1",
        "name": module_name,
        "date": date,
        "algebra": {
            "name": alg.name,
            "card": alg.card,
            "operations": [
                {"name": op.name, "arity": op.arity, "table": op.table}
                for op in alg.operations],
        },
        "lattice": {
            "name": lat.name,
            "size": lat.size,
            "meet": [list(row) for row in lat.meet],
            "join": [list(row) for row in lat.join],
        },
    }
    return json.dumps(payload, indent=2) + "\n"


# ---------------------------------------------------------------------------
# The survey: one target, one ground-set size, full report

def survey(lat: TargetLattice, n: int) -> Tuple[List[ClassReport], int]:
    """Search Eq(n) for the target, classify, and closure-test every class;
    returns the class reports and the total number of labelled copies."""
    eq = EqTables(n)
    copies = sublattice_copies(lat, eq)
    return ([closure_report(copy, size, eq)
             for copy, size in classify(copies, eq)], len(copies))


def survey_json(lat: TargetLattice, n: int, reports: Sequence[ClassReport],
                copies: int) -> str:
    """The deterministic JSON report of one survey."""
    payload = {
        "format": "flrp-eqsearch v1",
        "target": lat.name,
        "points": n,
        "copies": copies,
        "classes": [
            {
                "partitions": [list(p) for p in r.representative],
                "orbitSize": r.orbit_size,
                "groupOrder": r.group_order,
                "monoidSize": r.monoid_size,
                "properMaps": r.proper_maps,
                "invariants": r.invariants,
                "closed": r.closed,
            }
            for r in reports],
    }
    return json.dumps(payload, indent=2) + "\n"


def parse_target(path: Path) -> TargetLattice:
    """Read a target lattice from JSON: either a bare lattice stanza
    (name/size/meet/join) or a full claim file with a ``lattice`` field."""
    data = json.loads(path.read_text())
    stanza = data.get("lattice", data)
    lat = TargetLattice(
        name=str(stanza["name"]), size=int(stanza["size"]),
        meet=tuple(tuple(row) for row in stanza["meet"]),
        join=tuple(tuple(row) for row in stanza["join"]))
    validate_target(lat)
    return lat


def main(argv: Sequence[str]) -> int:
    args = [a for a in argv if a != "--fast"]
    fast = len(args) != len(argv)
    if len(args) not in (3, 5) or (len(args) == 5 and args[3] != "--json"):
        print("usage: eqsearch.py TARGET.json N [--fast] [--json REPORT.json]",
              file=sys.stderr)
        return 2
    lat = parse_target(Path(args[1]))
    n = int(args[2])
    if fast:
        try:
            from eqfast import survey_fast
        except ImportError:
            print("--fast needs numpy, which is not installed "
                  "(see the README's fast-backend note)", file=sys.stderr)
            return 2
        reports, copies = survey_fast(lat, n)
    else:
        reports, copies = survey(lat, n)
    closed = [r for r in reports if r.closed]
    print(f"{lat.name} in Eq({n}): {copies} labelled copies, "
          f"{len(reports)} classes, {len(closed)} closed")
    for k, r in enumerate(reports):
        verdict = "CLOSED" if r.closed else f"Inv(M) = {r.invariants}"
        print(f"  class {k}: orbit {r.orbit_size}, |G| = {r.group_order}, "
              f"|M| = {r.monoid_size} ({r.proper_maps} proper), {verdict}")
    if len(args) == 5:
        Path(args[4]).write_text(survey_json(lat, n, reports, copies))
        print(f"report written to {args[4]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
