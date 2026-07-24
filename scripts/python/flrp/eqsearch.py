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

The ``--group-rep`` flag (issue #494) restricts the sweep to copies all of
whose members are *uniform* partitions — every block of one size — the only
congruence lattices a transitive permutation group can produce (blocks of a
system of imprimitivity are cosets), mechanizing remark iv of the
SmallLatticeReps closure-algorithm discussion (§ 6.1).  Closure verdicts
keep their unrestricted meaning: the preserving monoid ranges over all
unary maps and ``Inv(M)`` over all of ``Eq(n)``, so a closed class still
yields an honest witness algebra; only the *negative* verdict weakens, to
"no algebra whose congruence lattice consists of uniform partitions" — see
the README's uniform-restriction note.

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
from collections import Counter
from dataclasses import dataclass
from itertools import combinations, permutations
from math import factorial
from pathlib import Path
from typing import (Dict, FrozenSet, Iterator, List, Optional, Sequence, Set,
                    Tuple, Union)

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


def is_uniform(p: Sequence[int]) -> bool:
    """Whether every block of the partition has the same size — there is a
    ``k`` (necessarily dividing ``n``) with every block of exactly ``k``
    elements.  Congruences of a transitive G-set are its systems of
    imprimitivity, whose blocks are cosets of a subgroup and hence all of
    one size; these are the only partitions the ``--group-rep`` sweep of
    issue #494 admits.  In a parent vector every index points at its block's
    least element, so the multiset of parent counts is the block-size
    profile."""
    return len(set(Counter(p).values())) == 1


def uniform_partitions(n: int) -> Tuple[Part, ...]:
    """Every uniform partition of ``range(n)`` — for each divisor ``k`` of
    ``n``, all partitions into blocks of exactly ``k`` elements, the bounds
    included (``k = 1`` is the diagonal, ``k = n`` the total relation) — in
    the canonical order of ``all_partitions``, without enumerating the full
    Bell(``n``) census.

    Each divisor's partitions are built directly as min-rooted parent
    vectors: the least unassigned element roots the next block, and its
    ``k − 1`` companions are drawn by ``combinations`` in lexicographic
    order.  Merging the divisors by sorting parent vectors lexicographically
    recovers exactly the enumeration order of ``all_partitions``: a
    restricted-growth string ranks blocks by first occurrence, i.e. by block
    minimum, so the lexicographic orders on restricted-growth strings and on
    normal-form parent vectors agree."""
    pool: List[Part] = []
    parent = [0] * n

    def blocks(remaining: Tuple[int, ...], k: int) -> Iterator[Part]:
        if not remaining:
            yield tuple(parent)
            return
        root, rest = remaining[0], remaining[1:]
        parent[root] = root
        for companions in combinations(rest, k - 1):
            for c in companions:
                parent[c] = root
            chosen = set(companions)
            yield from blocks(tuple(x for x in rest if x not in chosen), k)

    for k in (k for k in range(1, n + 1) if n % k == 0):
        pool.extend(blocks(tuple(range(n)), k))
    return tuple(sorted(pool))


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
        self.universe = self.parts      # Inv(M) ranges over all of Eq(n)
        size = len(self.parts)
        self.meet: List[List[int]] = [[0] * size for _ in range(size)]
        self.join: List[List[int]] = [[0] * size for _ in range(size)]
        for i in range(size):
            for j in range(i, size):
                m = self.index[partition_meet(self.parts[i], self.parts[j])]
                v = self.index[partition_join(self.parts[i], self.parts[j])]
                self.meet[i][j] = self.meet[j][i] = m
                self.join[i][j] = self.join[j][i] = v


class UniformTables:
    """Meet and join tables over the uniform pool only — the ``--group-rep``
    sweep of issue #494.  ``parts`` is ``uniform_partitions(n)``, bounds
    included, and a table entry is ``-1`` when the true meet or join in
    Eq(n) falls outside the pool; the embedding search reads that sentinel
    as a failed placement, which *is* the restriction's membership test (a
    meet or join of two uniform partitions need not be uniform).  The Snow
    closure test is NOT restricted: ``universe`` carries all of Eq(n), so
    preserving monoids, ``Inv(M)``, and closure verdicts mean exactly what
    they mean in the unrestricted sweep."""

    def __init__(self, n: int) -> None:
        self.n = n
        self.parts = uniform_partitions(n)
        self.index: Dict[Part, int] = {p: i for i, p in enumerate(self.parts)}
        self.bot = self.index[tuple(range(n))]
        self.top = self.index[(0,) * n]
        self.universe = all_partitions(n)
        size = len(self.parts)
        self.meet: List[List[int]] = [[0] * size for _ in range(size)]
        self.join: List[List[int]] = [[0] * size for _ in range(size)]
        for i in range(size):
            for j in range(i, size):
                m = self.index.get(
                    partition_meet(self.parts[i], self.parts[j]), -1)
                v = self.index.get(
                    partition_join(self.parts[i], self.parts[j]), -1)
                self.meet[i][j] = self.meet[j][i] = m
                self.join[i][j] = self.join[j][i] = v


# The sweep's table interface: the full Eq(n) tables or a restricted pool
# whose meet/join entries may be the out-of-pool sentinel -1.
Tables = Union[EqTables, UniformTables]


def sublattice_copies(lat: TargetLattice, eq: Tables) -> List[Copy]:
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
            value = (eq.meet if kind == "meet" else eq.join)[phi[u]][phi[v]]
            # -1 is the restricted tables' out-of-pool sentinel: the forced
            # value exists in Eq(n) but not in the sweep pool, so the
            # placement fails; full tables never produce it.
            candidates: Sequence[int] = (value,) if value >= 0 else ()
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


def _block_sizes(p: Sequence[int]) -> Tuple[int, ...]:
    """The block-size multiset of a partition, as a sorted tuple.  This is an
    invariant of the point relabeling action — two partitions in the same
    ``S_n`` orbit have the same block sizes — so it and anything built from it
    can be used to tell orbits apart without ever moving a point."""
    return tuple(sorted(Counter(p).values()))


def _relation_set_key(rels: Sequence[Part]) -> Tuple[object, ...]:
    """A relabeling-invariant, relation-order-independent key for the set of
    partitions ``rels``: the sorted block-size profiles of the members,
    paired with the sorted multiset of pairwise meet/join block-size profiles
    (each tagged by the endpoints' own profiles).  Every ingredient is an
    ``S_n`` invariant, so two relation sets in the same orbit always receive
    the same key — the key can never *split* an orbit.  Distinct orbits that
    happen to collide on it are not merged silently: the stabilizer
    conservation check in ``classify`` compares ``n!/|stab|`` against the
    number of relation sets bucketed here and fails loudly on a collision."""
    singles = sorted(_block_sizes(p) for p in rels)
    pairs = []
    for i in range(len(rels)):
        for j in range(i + 1, len(rels)):
            endpoints = tuple(sorted((_block_sizes(rels[i]), _block_sizes(rels[j]))))
            pairs.append((endpoints,
                          _block_sizes(partition_meet(rels[i], rels[j])),
                          _block_sizes(partition_join(rels[i], rels[j]))))
    return (tuple(singles), tuple(sorted(pairs)))


def _realizing(sources: Sequence[Part], targets: Sequence[Part], n: int,
               first_only: bool = False) -> int:
    """The number of point permutations ``π`` of ``range(n)`` that carry each
    ``sources[t]`` exactly onto ``targets[t]`` as ordered tuples of
    partitions — ``relabel(sources[t], π) == targets[t]`` for every ``t``
    (with ``first_only`` the search stops at the first such ``π``, returning
    ``0`` or ``1``, which is all an existence test needs).

    Found by backtracking over ``π(0), π(1), …``: assigning ``π(x) = y``
    forces, in every relation ``t``, the block of ``x`` in ``sources[t]`` to
    map to the block of ``y`` in ``targets[t]``, so the search maintains that
    partial block bijection (``fwd``) and its inverse (``bwd``) and prunes the
    instant a point's image would contradict an established correspondence or
    match blocks of different sizes."""
    m = len(sources)
    src_size = [Counter(s) for s in sources]
    tgt_size = [Counter(t) for t in targets]
    fwd: List[Dict[int, int]] = [dict() for _ in range(m)]
    bwd: List[Dict[int, int]] = [dict() for _ in range(m)]
    used = [False] * n
    count = 0
    stop = False

    def rec(x: int) -> None:
        nonlocal count, stop
        if x == n:
            count += 1
            stop = first_only
            return
        for y in range(n):
            if used[y]:
                continue
            touched: List[int] = []
            ok = True
            for t in range(m):
                sr, tr = sources[t][x], targets[t][y]
                if src_size[t][sr] != tgt_size[t][tr]:
                    ok = False
                    break
                mapped = fwd[t].get(sr)
                if mapped is not None:
                    if mapped != tr:
                        ok = False
                        break
                elif tr in bwd[t]:
                    ok = False
                    break
                else:
                    fwd[t][sr] = tr
                    bwd[t][tr] = sr
                    touched.append(t)
            if ok:
                used[y] = True
                rec(x + 1)
                used[y] = False
            for t in touched:
                del fwd[t][sources[t][x]]
                del bwd[t][targets[t][y]]
            if stop:
                return

    rec(0)
    return count


def _profile_perms(source_profiles: Sequence[Tuple[int, ...]],
                   target_profiles: Sequence[Tuple[int, ...]]
                   ) -> Iterator[Tuple[int, ...]]:
    """Every bijection ``σ`` of the relations that could match block-size
    profiles — ``source_profiles[i] == target_profiles[σ(i)]`` — the only
    ``σ`` a point permutation can realize.  Yields ``σ`` as an image tuple."""
    m = len(source_profiles)
    for perm in permutations(range(m)):
        if all(source_profiles[i] == target_profiles[perm[i]] for i in range(m)):
            yield perm


def _setwise_stabilizer_order(rels: Sequence[Part], n: int) -> int:
    """The order of the setwise stabilizer ``{π ∈ S_n : π·R = R}`` of the
    relation set ``R = set(rels)``.  A stabilizing permutation permutes the
    members of ``R`` among themselves, inducing a bijection ``σ`` of the
    relations; the stabilizer is the disjoint union, over every ``σ``, of the
    permutations that realize ``σ`` pointwise, so its order is the sum of
    those counts.  Only ``σ`` matching block-size profiles can contribute, so
    for a rigid copy only the identity does (the pointwise stabilizer), while
    for a copy with interchangeable relations (the three matchings of ``M3``)
    the relation-permuting ``σ`` contribute too — exactly the group whose
    index in ``S_n`` is the materialized orbit size."""
    profile = [_block_sizes(p) for p in rels]
    return sum(_realizing(rels, [rels[s[i]] for i in range(len(rels))], n)
               for s in _profile_perms(profile, profile))


def _setwise_iso(rels: Sequence[Part], other: Sequence[Part], n: int) -> bool:
    """Whether some point permutation carries the relation set ``set(rels)``
    onto ``set(other)`` — i.e. the two sublattices lie in one ``S_n`` orbit.
    Decomposes over the profile-compatible relation bijections ``σ`` exactly
    as the stabilizer does, asking only for existence of a realizing ``π``."""
    if len(rels) != len(other):
        return False
    pr = [_block_sizes(p) for p in rels]
    po = [_block_sizes(p) for p in other]
    return any(_realizing(rels, [other[s[i]] for i in range(len(rels))], n,
                          first_only=True)
               for s in _profile_perms(pr, po))


def _classify_orbit_stabilizer(copies: Sequence[Copy],
                               eq: Tables) -> List[Tuple[Copy, int]]:
    """Group the copies into orbits under relabeling of the points, by
    orbit–stabilizer rather than by materializing all ``n!`` relabelings
    (``12! ≈ 4.8 × 10⁸`` makes the materialized sweep hours per class).

    Copies are identified by their *unordered* relation sets (frozensets of
    partition indices): two embeddings differing only by an automorphism of
    the target lattice present the same sublattice of Eq(n), and the closure
    test of ``closure_report`` depends only on that relation set.  So this
    classifies sublattices rather than embeddings — orbit sizes count
    distinct relation sets, and the copy census may exceed the class-size
    total when the target has automorphisms.  Relabeling carries copies to
    copies and fixes the bounds, so the whole ``S_n`` orbit of any copy's
    relation set is itself present among the copies.

    Each distinct relation set is placed into a class by first hashing it to
    its relabeling-invariant key (the bounds are fixed by every permutation
    and carry no orbit information) and then, among the classes sharing that
    key, matching it against a representative by an explicit setwise
    isomorphism test — the invariant only narrows the isomorphism search, so
    distinct orbits that collide on it are still separated correctly.  The
    representative is the first copy reaching a class in the sorted copy
    order.  The orbit size is reported as ``n!/|stab|`` from a stabilizer
    backtrack, guarded by two cross-checks: per class ``n!/|stab|`` must equal
    the number of relation sets placed there, and globally the orbit sizes
    must sum to the number of distinct relation sets.  Returns one
    (first-found representative, orbit size) per class, in first-found order —
    byte-identical to the materialized classifier wherever both run."""
    bounds = (eq.bot, eq.top)
    first_copy: Dict[FrozenSet[int], Copy] = {}
    order: List[FrozenSet[int]] = []
    for copy in copies:
        key = frozenset(copy)
        if key not in first_copy:
            first_copy[key] = copy
            order.append(key)

    by_key: Dict[Tuple[object, ...], List[int]] = {}    # invariant key -> class indices
    reps: List[Copy] = []
    rep_rels: List[Tuple[Part, ...]] = []
    members: List[int] = []                             # distinct relation sets per class
    stabs: List[int] = []
    for key in order:
        rels = tuple(eq.parts[i] for i in sorted(key) if i not in bounds)
        siblings = by_key.setdefault(_relation_set_key(rels), [])
        idx = next((c for c in siblings if _setwise_iso(rels, rep_rels[c], eq.n)),
                   None)
        if idx is None:
            idx = len(reps)
            reps.append(first_copy[key])
            rep_rels.append(rels)
            members.append(0)
            stabs.append(_setwise_stabilizer_order(rels, eq.n))
            siblings.append(idx)
        members[idx] += 1

    fact = factorial(eq.n)
    classes: List[Tuple[Copy, int]] = []
    for idx, copy in enumerate(reps):
        stab = stabs[idx]
        if stab <= 0 or fact % stab != 0:
            raise CertificateError("stabilizer order does not divide n!")
        orbit = fact // stab
        if orbit != members[idx]:
            raise CertificateError(
                "orbit size n!/|stab| disagrees with the distinct relation "
                "sets in its class (stabilizer or isomorphism bug)")
        classes.append((copy, orbit))
    if sum(orbit for _, orbit in classes) != len(order):
        raise CertificateError("orbit sweep lost copies (relabeling bug)")
    return classes


def _classify_materialized(copies: Sequence[Copy],
                           eq: Tables) -> List[Tuple[Copy, int]]:
    """The reference classifier: for each new relation set, materialize its
    whole orbit by relabeling under every one of the ``n!`` point
    permutations and mark the images seen.  Simple and fast while ``n!`` is
    small; ``_classify_orbit_stabilizer`` is pinned byte-identical to it on
    every census where both run and takes over once ``n!`` makes this
    infeasible.  Same contract: one (first-found representative, orbit size)
    per class, in first-found order."""
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


# Materialize the orbit while n! is at most this (10! = 3,628,800), so the
# reference classifier runs for every committed census (n ≤ 8, and the empty
# uniform sweeps at 9 and 10); switch to orbit–stabilizer once n! makes
# materialization prohibitive — n ≥ 11, in particular the Eq(12) sweep.
_MATERIALIZE_LIMIT = factorial(10)


def classify(copies: Sequence[Copy], eq: Tables) -> List[Tuple[Copy, int]]:
    """Group the copies into orbits under relabeling of the points, returning
    one (first-found representative, orbit size) per class in first-found
    order.  Dispatches to the materialized-orbit reference while ``n!`` is
    small enough to enumerate and to the orbit–stabilizer classifier once it
    is not (``n ≥ 11``, i.e. the Eq(12) sweep) — the two are pinned
    byte-identical wherever both run, so the choice is invisible in the
    reports."""
    if factorial(eq.n) <= _MATERIALIZE_LIMIT:
        return _classify_materialized(copies, eq)
    return _classify_orbit_stabilizer(copies, eq)


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
                         eq: Tables) -> List[Part]:
    """The partitions preserved by every listed map — ``Inv(M)`` — filtered
    progressively; the identity and the constants preserve everything and
    are skipped.  The candidates are ``eq.universe``, all of Eq(n) even when
    the sweep pool is restricted: an algebra's congruence lattice is
    ``Inv`` of its unary polynomials over the *whole* partition lattice, so
    anything less would let a spurious closure verdict through."""
    identity = tuple(range(eq.n))
    candidates: List[Part] = list(eq.universe)
    for f in maps:
        if f == identity or len(set(f)) == 1:
            continue
        candidates = [p for p in candidates
                      if all(p[f[i]] == p[f[root]] for i, root in forest_edges(p))]
    return candidates


def closure_report(copy: Copy, orbit_size: int, eq: Tables) -> ClassReport:
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

def survey(lat: TargetLattice, n: int,
           uniform: bool = False) -> Tuple[List[ClassReport], int]:
    """Search Eq(n) for the target, classify, and closure-test every class;
    returns the class reports and the total number of labelled copies.
    With ``uniform`` the sweep is restricted to copies all of whose members
    are uniform partitions (the ``--group-rep`` restriction of issue #494);
    closure verdicts keep their unrestricted meaning."""
    eq: Tables = UniformTables(n) if uniform else EqTables(n)
    copies = sublattice_copies(lat, eq)
    return ([closure_report(copy, size, eq)
             for copy, size in classify(copies, eq)], len(copies))


def survey_json(lat: TargetLattice, n: int, reports: Sequence[ClassReport],
                copies: int, restriction: Optional[str] = None) -> str:
    """The deterministic JSON report of one survey.  ``restriction``
    (``"uniform"`` for a ``--group-rep`` sweep) is recorded between
    ``points`` and ``copies`` so a restricted census can never be mistaken
    for a full one; with the default ``None`` the payload is byte-for-byte
    the unrestricted ``flrp-eqsearch v1`` format."""
    payload = {
        "format": "flrp-eqsearch v1",
        "target": lat.name,
        "points": n,
        **({} if restriction is None else {"restriction": restriction}),
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
    args = [a for a in argv if a not in ("--fast", "--group-rep")]
    fast = "--fast" in argv
    uniform = "--group-rep" in argv
    if len(args) not in (3, 5) or (len(args) == 5 and args[3] != "--json"):
        print("usage: eqsearch.py TARGET.json N [--fast] [--group-rep] "
              "[--json REPORT.json]", file=sys.stderr)
        return 2
    lat = parse_target(Path(args[1]))
    n = int(args[2])
    if fast:
        try:
            from eqfast import survey_fast
        except ImportError:
            print("--fast needs numpy, which is not installed; the nix dev "
                  "shell ships it (`nix develop`), or see the README's "
                  "fast-backend note for other routes", file=sys.stderr)
            return 2
        reports, copies = survey_fast(lat, n, uniform=uniform)
    else:
        reports, copies = survey(lat, n, uniform=uniform)
    closed = [r for r in reports if r.closed]
    scope = " (uniform copies only)" if uniform else ""
    print(f"{lat.name} in Eq({n}){scope}: {copies} labelled copies, "
          f"{len(reports)} classes, {len(closed)} closed")
    for k, r in enumerate(reports):
        verdict = "CLOSED" if r.closed else f"Inv(M) = {r.invariants}"
        print(f"  class {k}: orbit {r.orbit_size}, |G| = {r.group_order}, "
              f"|M| = {r.monoid_size} ({r.proper_maps} proper), {verdict}")
    if len(args) == 5:
        Path(args[4]).write_text(survey_json(
            lat, n, reports, copies, "uniform" if uniform else None))
        print(f"report written to {args[4]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
