"""The Eq(12) ``--group-rep`` sweep for library ``L7`` (issue #499).

At twelve points the generic height-ordered assignment plan of ``eqsearch``
balloons — element 1 alone ranges over 32,032 uniform partitions, each with
~6,700 element-2 partners (meet ``Δ``), giving ~2.1 × 10⁸ level-2 prefixes and
a projected ~584 hours.  This module runs the same census to a verdict in
minutes with a **constraint-density, symmetry-broken** search specialised to
``L7``'s shape, and delegates classification counting and every closure test
to the shared, byte-parity-pinned engine of ``eqsearch``/``eqfast`` (PR #500).

The idea.  Anchor on the coatom ``(1,1) = (1,0) ∨ (0,1)``.  A coatom of a
uniform copy of ``L7`` has two distinct atoms below it, so its block size is a
proper composite divisor of 12 — only 4 or 6 — and ``S₁₂`` acts transitively on
the uniform partitions of a fixed block size, so the coatom may be fixed to the
two canonical representatives ``c₄``, ``c₆`` (every relabeling class has a copy
with the coatom in canonical form).  With the coatom pinned, the two atoms
below it are refinements (few), the second coatom ``(0,2)`` is pinned by
``(1,1) ∧ (0,2) = (0,1)``, and the doubly irreducible ``x`` is a transversal
atom — each step tightly constrained, so the tree is small.

Rigour.  For a class whose representative has coatom ``c_k``, exactly
``|Stab(c_k)| / |Stab(rep)|`` of its members carry that canonical coatom:
``Stab(rep) ≤ Stab(c_k)`` — forced by rigidity, since ``Aut(L7)`` is trivial,
so a relabeling fixing the relation set fixes every lattice role, the coatom
included — with ``|Stab(c_k)| = |S_k ≀ S_{12/k}|``; the divisibility this
subgroup relation implies is asserted at run time, not assumed.  Summing
over classes must reproduce the exhaustively counted number of canonical-coatom
copies; the sweep stops enumerating the instant that identity holds, which
*proves* every class has been found — no class can hide.  Every representative
is re-checked against the full ``L7`` tables, and every closure verdict is the
ordinary Snow test (the preserving monoid over *all* unary maps, ``Inv(M)`` over
all of ``Eq(12)``), identical to the smaller censuses.

Verdict (2026-07-24).  The census is non-empty — 15 classes — but **none is
closed**: every one has ``|M| = |G| + 12`` constants with no proper preserving
map, so ``Inv(M) = Inv(G) ≫ 7``.  Hence no algebra on twelve points has
``Con ≅ L7``; with the transitivity theorem and the antichain uniform pools at
13 (prime), 14 and 15, the minimal representation, if one exists, has at least
sixteen elements.  Committed as ``out/l7_eq12_uniform_report.json``.

This is a target-specialised sweep, not a generic engine; deriving the
constraint-density order automatically for an arbitrary target is the #486
follow-up.  The negative verdict cross-validates #487's degree-12 GAP scan.
"""

from __future__ import annotations

import random
import sys
from collections import defaultdict
from math import factorial
from pathlib import Path
from typing import Dict, Iterator, List, Tuple

from cg2 import CertificateError
from eqsearch import (ClassReport, Copy, LazyUniformTables, TargetLattice,
                      _setwise_iso, _setwise_stabilizer_order, closure_report,
                      survey_json, tables_from_leq)
from eqfast import FastLazyUniformTables

Cp = Tuple[int, int, int, int, int]     # pool indices of (π1, π2, π3, π4, π5)
FACT12 = factorial(12)
COATOM_BLOCK_SIZES = (4, 6)             # composite proper divisors of 12


def l7_target() -> TargetLattice:
    """``L7`` with the module numbering 0 = ⊥, 1 = (1,0), 2 = (0,1), 3 = x,
    4 = (1,1), 5 = (0,2), 6 = ⊤ (``Examples.Classical.Lattices.L7``)."""
    up = {0: {0, 1, 2, 3, 4, 5, 6}, 1: {1, 4, 6}, 2: {2, 4, 5, 6}, 3: {3, 6},
          4: {4, 6}, 5: {5, 6}, 6: {6}}
    leq = tuple(tuple(y in up[x] for y in range(7)) for x in range(7))
    return tables_from_leq("L7", leq)


def coatom_stabilizer_order(k: int, n: int = 12) -> int:
    """``|Stab_{S_n}(c_k)| = |S_k ≀ S_{n/k}| = (k!)^{n/k} · (n/k)!`` — the order
    of the stabilizer of the canonical uniform partition of block size ``k``."""
    return factorial(k) ** (n // k) * factorial(n // k)


_ORBIT_ORDER_SEED = 0x4C37       # pins the copy visiting order — see _copies


class _Anchor:
    """The pool facts needed to enumerate copies whose coatom π4 is fixed to
    the canonical block-size-``k`` partition ``c_k``: its refinements (atom
    candidates), the buckets of the pool by ``meet(c_k, ·)`` (so the atoms
    below a placed π2 and the second coatom are read off directly), and the
    partitions meeting ``c_k`` at ``Δ`` (transversal ``x`` candidates)."""

    def __init__(self, lz: LazyUniformTables, k: int) -> None:
        self.k = k
        self.p4 = lz.index[tuple((i // k) * k for i in range(12))]
        self.refine: List[int] = []
        self.bucket: Dict[int, List[int]] = defaultdict(list)
        for j in range(len(lz.parts)):
            if j in (lz.bot, lz.top):
                continue
            m = lz.meet_at(self.p4, j)
            self.bucket[m].append(j)
            if m == j:
                self.refine.append(j)
        self.delta = self.bucket.get(lz.bot, [])


def _copies(lz: LazyUniformTables, anc: _Anchor,
            diversify: bool) -> Iterator[Cp]:
    """Every copy of ``L7`` in ``Eq(12)`` whose coatom π4 is ``anc.p4``, as
    tuples ``(π1, π2, π3, π4, π5)``.  The constraints are exactly ``L7``'s: the
    atoms π1, π2 refine π4 with ``π1 ∨ π2 = π4`` and ``π1 ∧ π2 = Δ``; the second
    coatom π5 satisfies ``π4 ∧ π5 = π2``, ``π4 ∨ π5 = ∇``, ``π1 ∧ π5 = Δ`` and
    ``π1 ∨ π5 = ∇``; and π3 meets every placed relation at ``Δ`` and joins each
    to ``∇`` (the remaining incidences are implied, and every yielded tuple is
    re-verified against the full tables downstream).

    With ``diversify`` the atom candidates are visited in a fixed pseudo-random
    order (a seeded Mersenne Twister — byte-reproducible across CPython), so the
    dedup pass meets copies of every class within a few thousand tuples and the
    completeness stop fires early; without it (the exhaustive count pass) the
    natural order is used and the yield count is unaffected."""
    bot, top, p4 = lz.bot, lz.top, anc.p4
    meet, join = lz.meet_at, lz.join_at
    rng = random.Random(_ORBIT_ORDER_SEED) if diversify else None

    def ordered() -> List[int]:
        if rng is None:
            return anc.refine
        shuffled = anc.refine[:]
        rng.shuffle(shuffled)
        return shuffled

    for p1 in ordered():
        for p2 in ordered():
            if p2 == p1 or meet(p1, p2) != bot or join(p1, p2) != p4:
                continue
            for p5 in anc.bucket.get(p2, ()):
                if p5 in (p1, p2) or join(p4, p5) != top \
                        or meet(p1, p5) != bot or join(p1, p5) != top:
                    continue
                for p3 in anc.delta:
                    if p3 in (p1, p2, p5):
                        continue
                    if (meet(p3, p1) == bot and meet(p3, p2) == bot
                            and meet(p3, p5) == bot and join(p3, p1) == top
                            and join(p3, p2) == top and join(p3, p4) == top
                            and join(p3, p5) == top):
                        yield (p1, p2, p3, p4, p5)


def _verify_full(lz: LazyUniformTables, lat: TargetLattice, cp: Cp) -> bool:
    """Every one of the 49 pairwise meets and joins of ``(⊥, π1, …, π5, ⊤)``
    matches the ``L7`` tables — the untrusted search's output re-checked."""
    phi = (lz.bot, cp[0], cp[1], cp[2], cp[3], cp[4], lz.top)
    return all(lz.meet_at(phi[u], phi[v]) == phi[lat.meet[u][v]]
               and lz.join_at(phi[u], phi[v]) == phi[lat.join[u][v]]
               for u in range(7) for v in range(7))


def _orbits(lz: LazyUniformTables, lat: TargetLattice, anc: _Anchor,
            total: int) -> List[Tuple[Cp, int]]:
    """The relabeling classes among the copies with coatom ``anc.p4``: dedup by
    setwise isomorphism, keeping the first representative in the deterministic
    order, and stop as soon as ``Σ |Stab(c_k)|/|stab|`` reaches ``total`` — the
    completeness certificate that no class remains.  Each class's stabilizer
    order is checked to divide ``|Stab(c_k)|`` (it must: rigidity of ``L7``
    puts ``Stab(rep)`` inside ``Stab(c_k)``), so a violated assumption — say
    on a future target whose automorphisms swap coatom roles — fails loudly
    instead of silently corrupting the count.  Returns (representative,
    stabilizer order) per class."""
    anchor_stab = coatom_stabilizer_order(anc.k)
    reps: List[Tuple[Cp, Tuple, int]] = []
    covered = 0
    for cp in _copies(lz, anc, diversify=True):
        rels = tuple(lz.parts[j] for j in cp)
        if any(_setwise_iso(rels, r, 12) for _, r, _ in reps):
            continue
        if not _verify_full(lz, lat, cp):
            raise CertificateError(f"search produced a non-L7 copy: {cp}")
        stab = _setwise_stabilizer_order(rels, 12)
        if anchor_stab % stab != 0:
            raise CertificateError(
                f"coatom c_{anc.k}: stabilizer order {stab} does not divide "
                f"|Stab(c_{anc.k})| = {anchor_stab}, so Stab(rep) is not a "
                "subgroup of the anchor stabilizer and the completeness "
                "count would be invalid")
        reps.append((cp, rels, stab))
        covered += anchor_stab // stab
        if covered == total:
            break
    if covered != total:
        raise CertificateError(
            f"coatom c_{anc.k}: classes cover {covered} of {total} copies "
            "(orbit enumeration incomplete)")
    return [(cp, stab) for cp, _, stab in reps]


def sweep() -> Tuple[TargetLattice, List[ClassReport], int]:
    """Run the full ``Eq(12)`` uniform sweep for ``L7``: enumerate every
    relabeling class (over both coatom block sizes) with the completeness
    certificate, then closure-test each with the shared engine.  Returns the
    target, the class reports, and the total number of labelled copies."""
    lat = l7_target()
    lz = LazyUniformTables(12)
    flz = FastLazyUniformTables(12)         # vectorized Inv(M) over Bell(12)
    classes: List[Tuple[Cp, int]] = []
    for k in COATOM_BLOCK_SIZES:
        anc = _Anchor(lz, k)
        total = sum(1 for _ in _copies(lz, anc, diversify=False))
        classes.extend(_orbits(lz, lat, anc, total))
    reports = [closure_report((lz.bot, cp[0], cp[1], cp[2], cp[3], cp[4], lz.top),
                              FACT12 // stab, flz)
               for cp, stab in classes]
    copies = sum(FACT12 // stab for _, stab in classes)
    return lat, reports, copies


def main(argv: List[str]) -> int:
    out = None
    if len(argv) == 3 and argv[1] == "--json":
        out = Path(argv[2])
    elif len(argv) != 1:
        print("usage: eq12_uniform_sweep.py [--json REPORT.json]", file=sys.stderr)
        return 2
    lat, reports, copies = sweep()
    closed = [r for r in reports if r.closed]
    print(f"L7 in Eq(12) (uniform copies only): {copies} labelled copies, "
          f"{len(reports)} classes, {len(closed)} closed")
    for k, r in enumerate(reports):
        verdict = "CLOSED" if r.closed else f"Inv(M) = {r.invariants}"
        print(f"  class {k}: orbit {r.orbit_size}, |G| = {r.group_order}, "
              f"|M| = {r.monoid_size} ({r.proper_maps} proper), {verdict}")
    if out is not None:
        out.write_text(survey_json(lat, 12, reports, copies, restriction="uniform"))
        print(f"report written to {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
