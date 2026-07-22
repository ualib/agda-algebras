"""Tests for the WP-6 certificate emitter (`make flrp-test`).

Three layers, mirroring the pipeline's trust story:

+ engine unit tests — cg2 worklist, union-find normal form, lattice
  construction, target matching, and the renderer's guard rails;
+ a Python mirror of the Agda checker's obligations (C1 trace soundness,
  C2 replay coverage, C3 seed containment), run over every trace the pilot
  certificate contains — an engine-side regression tripwire only, never a
  substitute for the Agda checker, which remains the sole authority;
+ golden round-trip tests — re-emitting the committed pilot input must
  reproduce the committed ``.lagda.md`` module and audit JSON byte for byte
  (the emitter is a deterministic function of its input).

The Agda side needs no harness of its own: the emitted pilot module is part
of the library, so ``make check`` — the repository's single test gate — is
exactly the end-to-end verification of the certificate.
"""

from __future__ import annotations

import json
import unittest
from typing import Sequence, Tuple

from cg2 import (Algebra, CertificateError, CgResult, Merge, Operation, Pair,
                 SeedJust, TranslateJust, UnionFind, congruence_generated_by,
                 forest_edges, validate_algebra)
from emit_agda import (REPO_ROOT, certificate_json, emitted_module, fin,
                       merge_str, parse_input)
from lattice import (TargetLattice, WholeLatticeCertificate, build_certificate,
                     congruence_lattice, match_target, partition_meet,
                     validate_lattice)

PILOT_INPUT = REPO_ROOT / "scripts" / "flrp" / "inputs" / "v4_regular_m3.json"
PILOT_MODULE = REPO_ROOT / "src" / "FLRP" / "Certificates" / "Pilot" / "V4RegularM3.lagda.md"
PILOT_AUDIT = REPO_ROOT / "scripts" / "flrp" / "out" / "V4RegularM3.cert.json"


def v4() -> Algebra:
    """The Klein four-group acting on itself (the pilot algebra)."""
    tables = {"e": [0, 1, 2, 3], "a": [1, 0, 3, 2], "b": [2, 3, 0, 1], "ab": [3, 2, 1, 0]}
    return Algebra(
        name="V4 regular",
        card=4,
        operations=tuple(Operation(name, 1, t) for name, t in tables.items()))


def m3() -> TargetLattice:
    """The five-element modular lattice M3 (the pilot target)."""
    return TargetLattice(
        name="M3", size=5,
        meet=((0, 0, 0, 0, 0), (0, 1, 0, 0, 1), (0, 0, 2, 0, 2),
              (0, 0, 0, 3, 3), (0, 1, 2, 3, 4)),
        join=((0, 1, 2, 3, 4), (1, 1, 4, 4, 4), (2, 4, 2, 4, 4),
              (3, 4, 4, 3, 4), (4, 4, 4, 4, 4)))


def chain5() -> TargetLattice:
    """A five-element chain: same size as M3, not isomorphic to Con(V4)."""
    rng = range(5)
    return TargetLattice(
        name="chain5", size=5,
        meet=tuple(tuple(min(k, l) for l in rng) for k in rng),
        join=tuple(tuple(max(k, l) for l in rng) for k in rng))


# ---------------------------------------------------------------------------
# The Agda checker's obligations, mirrored (engine-side tripwire only)

def check_trace(alg: Algebra, seeds: Sequence[Pair], trace: Sequence[Merge],
                claimed: Sequence[int]) -> None:
    """Assert C1 (every merge justified), C2 (the replay covers the claimed
    partition), and C3's seed half (the claimed partition respects the
    seeds), exactly as the Agda checker states them."""
    merged: list[Pair] = []
    for position, m in enumerate(trace):
        why = m.why
        if isinstance(why, SeedJust):
            assert 0 <= why.seed < len(seeds), "seed reference out of range"
            assert seeds[why.seed] == (m.lhs, m.rhs), "seed pair mismatch"
        else:
            assert isinstance(why, TranslateJust)
            assert 0 <= why.ref < position, "translate must reference an earlier merge"
            op = alg.operations[why.op]
            assert 0 <= why.coord < op.arity and len(why.frozen) == op.arity
            x, y = merged[why.ref]

            def image(z: int) -> int:
                args = why.frozen[:why.coord] + (z,) + why.frozen[why.coord + 1:]
                return op.apply(args)

            assert (m.lhs, m.rhs) == (image(x), image(y)), "translate image mismatch"
        merged.append((m.lhs, m.rhs))

    replay = UnionFind(alg.card)
    for u, v in merged:
        replay.union(u, v)
    for i in range(alg.card):
        assert replay.find(claimed[i]) == replay.find(i), "replay does not cover the claim"
    for a, b in seeds:
        assert claimed[a] == claimed[b], "claimed partition drops a seed pair"


def check_certificate(alg: Algebra, target: TargetLattice,
                      cert: WholeLatticeCertificate) -> None:
    """Run check_trace over every trace of a whole-lattice certificate, plus
    the pointer-structure sanity the Agda checker also demands."""
    n, m = alg.card, target.size
    diagonal = tuple(range(n))
    assert cert.parts[cert.bot] == diagonal
    assert cert.meet == target.meet and cert.join == target.join
    for pv in cert.parts:
        assert all(pv[pv[i]] == pv[i] and pv[i] <= i for i in range(n)), "not normal form"
    assert len(set(cert.parts)) == m, "entry list has duplicates"
    for i in range(n):
        for j in range(n):
            check_trace(alg, [(i, j)], cert.prin_traces[i][j], cert.parts[cert.prin[i][j]])
    for k in range(m):
        for l in range(m):
            seeds = forest_edges(cert.parts[k]) + forest_edges(cert.parts[l])
            check_trace(alg, seeds, cert.join_traces[k][l], cert.parts[cert.join[k][l]])


# ---------------------------------------------------------------------------

class Cg2Tests(unittest.TestCase):

    def test_operation_apply(self) -> None:
        op = Operation("f", 2, [[0, 1], [1, 0]])
        self.assertEqual(op.apply((1, 0)), 1)
        with self.assertRaises(CertificateError):
            op.apply((1,))

    def test_validate_algebra_rejects_bad_tables(self) -> None:
        with self.assertRaises(CertificateError):
            validate_algebra(Algebra("bad", 2, (Operation("f", 1, [0, 5]),)))
        with self.assertRaises(CertificateError):
            validate_algebra(Algebra("bad", 2, (Operation("f", 1, [0]),)))
        validate_algebra(v4())

    def test_normal_form_is_min_rooted(self) -> None:
        uf = UnionFind(4)
        uf.union(3, 1)
        uf.union(1, 2)
        self.assertEqual(uf.normal_form(4), (0, 1, 1, 1))

    def test_forest_edges_order(self) -> None:
        self.assertEqual(forest_edges((0, 0, 2, 2)), [(1, 0), (3, 2)])
        self.assertEqual(forest_edges((0, 1, 2, 3)), [])

    def test_principal_congruence_of_v4(self) -> None:
        run = congruence_generated_by(v4(), [(0, 1)])
        self.assertEqual(run.parent, (0, 0, 2, 2))
        self.assertEqual(len(run.trace), 2)
        self.assertIsInstance(run.trace[0].why, SeedJust)
        self.assertIsInstance(run.trace[1].why, TranslateJust)
        check_trace(v4(), [(0, 1)], run.trace, run.parent)

    def test_diagonal_principal_is_trivial(self) -> None:
        run = congruence_generated_by(v4(), [(2, 2)])
        self.assertEqual(run.parent, (0, 1, 2, 3))
        self.assertEqual(run.trace, ())

    def test_all_principal_runs_check(self) -> None:
        alg = v4()
        for i in range(alg.card):
            for j in range(alg.card):
                run = congruence_generated_by(alg, [(i, j)])
                check_trace(alg, [(i, j)], run.trace, run.parent)


class LatticeTests(unittest.TestCase):

    def test_partition_meet(self) -> None:
        self.assertEqual(partition_meet((0, 0, 2, 2), (0, 1, 0, 1)), (0, 1, 2, 3))
        self.assertEqual(partition_meet((0, 0, 0, 0), (0, 0, 2, 2)), (0, 0, 2, 2))

    def test_con_v4_is_m3(self) -> None:
        parts, _, _ = congruence_lattice(v4())
        self.assertEqual(len(parts), 5)
        self.assertIn((0, 1, 2, 3), parts)          # the diagonal
        self.assertIn((0, 0, 0, 0), parts)          # the total congruence
        self.assertIn((0, 0, 2, 2), parts)          # the three coset partitions
        self.assertIn((0, 1, 0, 1), parts)
        self.assertIn((0, 1, 1, 0), parts)

    def test_match_target_rejects_wrong_lattice(self) -> None:
        parts, index, _ = congruence_lattice(v4())
        with self.assertRaises(CertificateError):
            match_target(v4(), parts, index, chain5())

    def test_build_certificate_checks_out(self) -> None:
        cert = build_certificate(v4(), m3())
        check_certificate(v4(), m3(), cert)

    def test_false_claim_is_rejected(self) -> None:
        broken = TargetLattice(name="M3-broken", size=5,
                               meet=m3().meet,
                               join=tuple(tuple(4 if (k, l) == (1, 1) else v
                                                for l, v in enumerate(row))
                                          for k, row in enumerate(m3().join)))
        validate_lattice(broken)
        with self.assertRaises(CertificateError):
            build_certificate(v4(), broken)


class EmitterTests(unittest.TestCase):

    def test_fin_literal_range(self) -> None:
        self.assertEqual(fin(9), "9F")
        with self.assertRaises(CertificateError):
            fin(10)

    def test_merge_str_uses_backward_offsets(self) -> None:
        m = Merge(2, 3, TranslateJust(op=1, coord=0, frozen=(0,), ref=0))
        self.assertEqual(merge_str(2, m),
                         "mkMerge 2F 3F (translate 1F 0F (0F ∷ []) 1)")
        with self.assertRaises(CertificateError):
            merge_str(0, m)   # a forward reference must be rejected

    def test_renderer_rejects_nonunary_signatures(self) -> None:
        alg = Algebra("binary", 2, (Operation("f", 2, [[0, 1], [1, 0]]),))
        target = TargetLattice("chain2", 2, ((0, 0), (0, 1)), ((0, 1), (1, 1)))
        cert = build_certificate(alg, target)
        with self.assertRaises(CertificateError):
            emitted_module("Bad", "2026-01-01", alg, target, cert, "x.json")

    def test_parse_input_validates(self) -> None:
        name, date, algebra, target = parse_input(PILOT_INPUT)
        self.assertEqual((name, date), ("V4RegularM3", "2026-07-22"))
        self.assertEqual(algebra.card, 4)
        self.assertEqual(target.size, 5)

    def test_golden_module(self) -> None:
        """Re-emitting the pilot input reproduces the committed module."""
        name, date, algebra, target = parse_input(PILOT_INPUT)
        cert = build_certificate(algebra, target)
        rendered = emitted_module(name, date, algebra, target, cert,
                                  "scripts/flrp/inputs/v4_regular_m3.json")
        self.assertEqual(rendered, PILOT_MODULE.read_text())

    def test_golden_audit_json(self) -> None:
        """Re-emitting the pilot input reproduces the committed audit JSON,
        and that JSON is well formed."""
        name, _, algebra, target = parse_input(PILOT_INPUT)
        cert = build_certificate(algebra, target)
        rendered = certificate_json(name, algebra, target, cert)
        self.assertEqual(rendered, PILOT_AUDIT.read_text())
        self.assertEqual(json.loads(rendered)["format"], "flrp-cert v1")


if __name__ == "__main__":
    unittest.main()
