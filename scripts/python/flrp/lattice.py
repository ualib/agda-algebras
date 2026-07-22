"""Whole congruence lattices with certificates.

File: scripts/python/flrp/lattice.py

Description:

  Builds, for a finite algebra given by tables, the complete
  ``WholeLatticeCertificate`` of the WP-6 pipeline (issue #457): the list of all
  congruences as normal-form parent vectors, the principal-congruence pointer
  table with Freese traces, and the meet and join tables (joins with traces) —
  relabeled to match a claimed target lattice, so that the certificate's meet
  table is *syntactically* the target's, which is what the Agda side's
  ``MeetMatches`` check pins.

Engine-side mathematics:

  Never trusted, always re-checked in Agda.

  + every congruence of a finite algebra is a join of principal congruences, so
    closing the principal congruences under binary join (computed by ``cg2``
    runs seeded with both arguments' forest edges) enumerates the whole lattice;
  + the meet of two congruences is their pointwise root-pair intersection, a
    pure partition operation;
  + the claimed isomorphism with the target lattice is found by (bounded)
    search over index bijections and then discharged definitionally by the
    checker.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import permutations
from typing import Dict, List, Sequence, Tuple

from cg2 import (Algebra, CertificateError, CgResult, Merge, Pair,
                 congruence_generated_by, forest_edges)

Table = Tuple[Tuple[int, ...], ...]
TraceTable = Tuple[Tuple[Tuple[Merge, ...], ...], ...]


@dataclass(frozen=True)
class TargetLattice:
    """The claimed congruence lattice, by its meet and join tables."""

    name: str
    size: int
    meet: Table
    join: Table


@dataclass(frozen=True)
class WholeLatticeCertificate:
    """The whole-lattice certificate, indexed by the target lattice's
    carrier (``Setoid.Congruences.Certificates.Schema.LatticeCert``)."""

    parts: Tuple[Tuple[int, ...], ...]
    bot: int
    prin: Table
    prin_traces: TraceTable
    meet: Table
    join: Table
    join_traces: TraceTable


def validate_lattice(lat: TargetLattice) -> None:
    """Check the target tables have the right shape and in-range entries."""
    for name, table in (("meet", lat.meet), ("join", lat.join)):
        if len(table) != lat.size or any(len(row) != lat.size for row in table):
            raise CertificateError(f"lattice {lat.name}: {name} table has wrong shape")
        if any(not 0 <= v < lat.size for row in table for v in row):
            raise CertificateError(f"lattice {lat.name}: {name} entry out of range")


def partition_meet(p: Sequence[int], q: Sequence[int]) -> Tuple[int, ...]:
    """The meet of two partitions, as a normal-form parent vector: blocks are
    the nonempty root-pair intersections, labeled by their least members."""
    least: Dict[Pair, int] = {}
    for i, key in enumerate(zip(p, q)):
        least.setdefault(key, i)
    return tuple(least[(p[i], q[i])] for i in range(len(p)))


def congruence_join(alg: Algebra, p: Sequence[int], q: Sequence[int]) -> CgResult:
    """The join of two congruences: cg2 seeded with both edge lists.  (The
    join in Con(A) is Cg of the union, which is generally coarser than the
    partition join; the worklist supplies the operation closure.)"""
    return congruence_generated_by(alg, forest_edges(p) + forest_edges(q))


def congruence_lattice(
    alg: Algebra,
) -> Tuple[List[Tuple[int, ...]], Dict[Tuple[int, ...], int], Dict[Pair, CgResult]]:
    """All congruences of the algebra: the principal congruences of every
    carrier pair, closed under binary join.  Returns the congruence list (in
    deterministic discovery order), its index, and the principal runs."""
    principal: Dict[Pair, CgResult] = {
        (i, j): congruence_generated_by(alg, [(i, j)])
        for i in range(alg.card) for j in range(alg.card)
    }

    parts: List[Tuple[int, ...]] = []
    index: Dict[Tuple[int, ...], int] = {}

    def add(pv: Tuple[int, ...]) -> bool:
        if pv not in index:
            index[pv] = len(parts)
            parts.append(pv)
            return True
        return False

    for run in principal.values():
        add(run.parent)

    grown = True
    while grown:
        snapshot = list(parts)
        grown = False
        for p in snapshot:
            for q in snapshot:
                if add(congruence_join(alg, p, q).parent):
                    grown = True

    return parts, index, principal


def match_target(
    alg: Algebra,
    parts: List[Tuple[int, ...]],
    index: Dict[Tuple[int, ...], int],
    target: TargetLattice,
) -> Tuple[int, ...]:
    """A bijection sigma from target-lattice indices to congruence indices
    respecting both tables, or a CertificateError if none exists.  Bounded
    brute force — adequate for the small-lattice frontier this pipeline
    serves; the checker re-verifies everything, so nothing rides on this
    search being clever."""
    m = target.size
    if m != len(parts):
        raise CertificateError(
            f"Con({alg.name}) has {len(parts)} congruences, "
            f"but {target.name} has {m} elements")
    if m > 8:
        raise CertificateError(
            f"refusing a brute-force search over {m}! bijections; "
            "add pruning to match_target first")

    meet_of: Dict[Pair, int] = {
        (k, l): index[partition_meet(parts[k], parts[l])]
        for k in range(m) for l in range(m)
    }
    join_of: Dict[Pair, int] = {
        (k, l): index[congruence_join(alg, parts[k], parts[l]).parent]
        for k in range(m) for l in range(m)
    }

    for sigma in permutations(range(m)):
        if all(sigma[target.meet[k][l]] == meet_of[(sigma[k], sigma[l])]
               and sigma[target.join[k][l]] == join_of[(sigma[k], sigma[l])]
               for k in range(m) for l in range(m)):
            return sigma
    raise CertificateError(
        f"Con({alg.name}) is not isomorphic to {target.name} "
        "under any index bijection")


def build_certificate(alg: Algebra, target: TargetLattice) -> WholeLatticeCertificate:
    """The whole-lattice certificate for the claim Con(alg) ≅ target,
    relabeled so that entry k of the certificate is the congruence matching
    lattice element k.  Raises CertificateError if the claim is false."""
    parts0, index0, principal = congruence_lattice(alg)
    sigma = match_target(alg, parts0, index0, target)
    m = target.size

    inverse: Dict[int, int] = {sigma[k]: k for k in range(m)}
    parts: Tuple[Tuple[int, ...], ...] = tuple(parts0[sigma[k]] for k in range(m))

    diagonal = tuple(range(alg.card))
    bot = inverse[index0[diagonal]]
    if any(target.meet[bot][l] != bot for l in range(m)):
        raise CertificateError("the diagonal does not sit at the target's bottom")

    prin: Table = tuple(
        tuple(inverse[index0[principal[(i, j)].parent]] for j in range(alg.card))
        for i in range(alg.card))
    prin_traces: TraceTable = tuple(
        tuple(principal[(i, j)].trace for j in range(alg.card))
        for i in range(alg.card))

    join_runs: Dict[Pair, CgResult] = {
        (k, l): congruence_join(alg, parts[k], parts[l])
        for k in range(m) for l in range(m)
    }
    for (k, l), run in join_runs.items():
        if run.parent != parts[target.join[k][l]]:
            raise CertificateError(f"join table mismatch at ({k}, {l})")
        if partition_meet(parts[k], parts[l]) != parts[target.meet[k][l]]:
            raise CertificateError(f"meet table mismatch at ({k}, {l})")

    return WholeLatticeCertificate(
        parts=parts,
        bot=bot,
        prin=prin,
        prin_traces=prin_traces,
        meet=target.meet,
        join=target.join,
        join_traces=tuple(
            tuple(join_runs[(k, l)].trace for l in range(m)) for k in range(m)),
    )
