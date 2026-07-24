"""Tests for the Eq(n) search and Snow closure tools (`make flrp-test`).

Three layers, mirroring ``test_flrp.py``:

+ unit tests for the partition kernel, cross-validated against brute force
  (the backtracking monoid enumeration is compared with a full scan of all
  ``n^n`` maps on small carriers, so no golden number is trusted twice);
+ reproduction of the 2026-07-22 ``L7`` session results (issues #484, #486):
  no copies in Eq(4) or Eq(5); 1080 labelled copies in Eq(6) falling into
  exactly two relabeling classes, neither closed, with the session's
  stabilizer orders and ``Inv(M)`` sizes; the Eq(7) sweep (55,440 copies,
  12 classes, none closed) runs only with ``FLRP_EQSEARCH_SLOW=1``;
+ the end-to-end loop: the search finds the closed matchings class for
  ``M3`` on 4 points, its witness algebra flows through ``lattice.py``'s
  certificate builder against the pilot's ``M3`` tables, and the mirrored
  checker obligations of ``test_flrp.py`` all pass — search to certificate
  with no manual step.
"""

from __future__ import annotations

import json
import os
import tempfile
import unittest
from collections import Counter
from itertools import product
from pathlib import Path
from typing import List, Sequence, Tuple

import contextlib
import io

from cg2 import CertificateError
from eqsearch import (ClassReport, EqTables, Part, UniformTables,
                      _classify_materialized, _classify_orbit_stabilizer,
                      _setwise_stabilizer_order, all_partitions, claim_input,
                      classify, closed_class_algebra, closure_report,
                      invariant_partitions, is_uniform, main, partition_join,
                      preserving_maps, relabel, sublattice_copies, survey,
                      survey_json, tables_from_leq, uniform_partitions,
                      validate_target)
from lattice import TargetLattice, build_certificate, partition_meet
from test_flrp import check_certificate, m3

BELL = {1: 1, 2: 2, 3: 5, 4: 15, 5: 52, 6: 203}


def l7() -> TargetLattice:
    """The seven-element lattice `L7` of `Examples.Classical.Lattices.L7`
    (`L10` of DeMeo–Freese–Jipsen), with the module's element numbering:
    0 = ⊥, 1 = (1,0), 2 = (0,1), 3 = x, 4 = (1,1), 5 = (0,2), 6 = ⊤."""
    up = {0: {0, 1, 2, 3, 4, 5, 6}, 1: {1, 4, 6}, 2: {2, 4, 5, 6},
          3: {3, 6}, 4: {4, 6}, 5: {5, 6}, 6: {6}}
    leq = tuple(tuple(y in up[x] for y in range(7)) for x in range(7))
    return tables_from_leq("L7", leq)


def brute_force_maps(relations: Sequence[Part], n: int) -> List[Tuple[int, ...]]:
    """All relation-preserving unary maps by full scan — the independent
    oracle the backtracking enumeration is checked against."""
    return [f for f in product(range(n), repeat=n)
            if all(all(r[f[x]] == r[f[y]] for x in range(n) for y in range(n)
                       if r[x] == r[y])
                   for r in relations)]


class PartitionKernelTests(unittest.TestCase):

    def test_partition_counts_are_bell_numbers(self) -> None:
        """kernel: Eq(n) enumeration hits the Bell numbers for n ≤ 6."""
        for n, bell in BELL.items():
            self.assertEqual(len(all_partitions(n)), bell)

    def test_partitions_are_normal_form(self) -> None:
        """kernel: every enumerated partition is a min-rooted parent vector."""
        for pv in all_partitions(5):
            self.assertTrue(all(pv[pv[i]] == pv[i] and pv[i] <= i
                                for i in range(5)))

    def test_join_and_meet(self) -> None:
        """kernel: partition join is the transitive closure, meet the refinement."""
        self.assertEqual(partition_join((0, 0, 2, 3), (0, 1, 1, 3)), (0, 0, 0, 3))
        self.assertEqual(partition_meet((0, 0, 0, 3), (0, 0, 2, 2)), (0, 0, 2, 3))

    def test_relabel_is_an_action(self) -> None:
        """kernel: relabeling acts blockwise, moves asymmetric partitions, and is invertible."""
        p = (0, 0, 0, 3, 3, 5)                    # |0,1,2|3,4|5|
        rev = (5, 4, 3, 2, 1, 0)
        self.assertEqual(relabel(p, rev), (0, 1, 1, 3, 3, 3))    # |0|1,2|3,4,5|
        self.assertEqual(relabel(relabel(p, rev), rev), p)
        cyc = (1, 2, 0, 3, 4, 5)                  # the 3-cycle 0 -> 1 -> 2 -> 0
        self.assertEqual(relabel((0, 0, 2, 2, 4, 4), cyc), (0, 1, 1, 0, 4, 4))

    def test_preserving_maps_match_brute_force(self) -> None:
        """kernel: backtracking monoid enumeration agrees with the n^n scan."""
        eq = EqTables(4)
        matchings = [(0, 0, 2, 2), (0, 1, 0, 1), (0, 1, 1, 0)]
        self.assertEqual(sorted(preserving_maps(matchings, 4)),
                         brute_force_maps(matchings, 4))
        mixed = [(0, 0, 2, 2), (0, 1, 0, 1), (0, 1, 2, 0)]
        self.assertEqual(sorted(preserving_maps(mixed, 4)),
                         brute_force_maps(mixed, 4))
        self.assertEqual(len(invariant_partitions([(0, 1, 2, 3)], eq)), 15)


class UniformPoolTests(unittest.TestCase):
    """The uniform (coset-block) pool enumerator of issue #494."""

    def test_uniform_pool_counts(self) -> None:
        """pool: nontrivial uniform counts and block-size shapes match #494's table."""
        expected = {6: {2: 15, 3: 10}, 7: {}, 8: {2: 105, 4: 35},
                    9: {3: 280}, 10: {2: 945, 5: 126}}
        for n, shapes in expected.items():
            pool = uniform_partitions(n)
            self.assertEqual(pool[0], (0,) * n)              # ∇ sorts first
            self.assertEqual(pool[-1], tuple(range(n)))      # Δ sorts last
            nontrivial = [p for p in pool
                          if p not in ((0,) * n, tuple(range(n)))]
            self.assertEqual(len(nontrivial), sum(shapes.values()))
            by_size = Counter(n // len(set(p)) for p in nontrivial)
            self.assertEqual(dict(by_size), shapes)

    def test_uniform_pool_is_canonical_subsequence(self) -> None:
        """pool: the per-divisor enumerator equals the Bell filter, order included (n ≤ 8)."""
        for n in range(1, 9):
            self.assertEqual(uniform_partitions(n),
                             tuple(p for p in all_partitions(n)
                                   if is_uniform(p)))

    def test_is_uniform_spot_checks(self) -> None:
        """pool: the bounds are uniform; the L7 grid element |0,2|3,4| on six points is not."""
        self.assertTrue(is_uniform(tuple(range(6))))
        self.assertTrue(is_uniform((0,) * 6))
        self.assertTrue(is_uniform((0, 1, 0, 3, 3, 1)))      # |0,2|1,5|3,4|
        self.assertFalse(is_uniform((0, 1, 0, 3, 3, 5)))     # |0,2|3,4| + singletons


class UniformSweepTests(unittest.TestCase):
    """The --group-rep restriction (issue #494): pool tables with the
    out-of-pool sentinel, closure over the full Eq(n) universe, and filter
    parity — the restricted census must be exactly the all-uniform subset
    of the unrestricted one."""

    def test_uniform_tables_sentinel_and_universe(self) -> None:
        """uniform: Eq(6) pool tables agree with the full tables where the result stays in the pool, are -1 where it leaves, and Inv ranges over all 203 partitions."""
        eq, ut = EqTables(6), UniformTables(6)
        self.assertEqual(ut.parts, uniform_partitions(6))
        self.assertEqual(len(ut.parts), 27)
        self.assertEqual(ut.universe, all_partitions(6))
        for i, p in enumerate(ut.parts):
            for j, q in enumerate(ut.parts):
                meet = eq.parts[eq.meet[eq.index[p]][eq.index[q]]]
                join = eq.parts[eq.join[eq.index[p]][eq.index[q]]]
                self.assertEqual(ut.meet[i][j], ut.index.get(meet, -1))
                self.assertEqual(ut.join[i][j], ut.index.get(join, -1))
        # |0,1|2,3|4,5| ∨ |0,2|1,3|4,5| = |0,1,2,3|4,5|: uniform arguments,
        # non-uniform join — the sentinel is exercised, not hypothetical
        self.assertEqual(
            ut.join[ut.index[(0, 0, 2, 2, 4, 4)]][ut.index[(0, 1, 0, 1, 4, 4)]],
            -1)
        # the empty monoid constrains nothing: Inv is all of Eq(6), not the pool
        self.assertEqual(len(invariant_partitions([], ut)), 203)

    def _filter_parity(self, lat: TargetLattice,
                       n: int) -> Tuple[List[ClassReport], int]:
        """Assert the uniform survey equals the all-uniform subset of the
        full survey, class report for class report, and return it."""
        full_reports, _ = survey(lat, n)
        uni_reports, uni_copies = survey(lat, n, uniform=True)
        self.assertEqual(uni_reports,
                         [r for r in full_reports
                          if all(is_uniform(p) for p in r.representative)])
        return uni_reports, uni_copies

    def test_m3_eq4_uniform_keeps_the_matchings_class(self) -> None:
        """uniform: the M3/Eq(4) --group-rep census is exactly the closed matchings class — the restriction keeps real transitive representations."""
        reports, copies = self._filter_parity(m3(), 4)
        self.assertEqual(copies, 6)
        self.assertEqual([r.closed for r in reports], [True])

    def test_m3_eq6_uniform_filter_parity(self) -> None:
        """uniform: the M3/Eq(6) --group-rep census (840 copies, 3 open classes) equals the all-uniform subset of the full census."""
        reports, copies = self._filter_parity(m3(), 6)
        self.assertEqual(copies, 840)
        self.assertEqual(
            [(r.orbit_size, r.group_order, r.monoid_size, r.proper_maps,
              r.invariants, r.closed) for r in reports],
            [(60, 6, 12, 0, 6, False), (60, 2, 10, 2, 22, False),
             (20, 6, 12, 0, 6, False)])

    def test_l7_eq6_uniform_census_is_empty(self) -> None:
        """uniform: the L7/Eq(6) --group-rep census is EMPTY — both known classes contain the non-uniform grid element |0,2|3,4|."""
        reports, copies = self._filter_parity(l7(), 6)
        self.assertEqual((reports, copies), ([], 0))

    def test_l7_eq7_uniform_pool_degenerates(self) -> None:
        """uniform: 7 is prime, so the pool is the bounds alone and the L7 sweep is empty — a transitive action of prime degree is primitive."""
        self.assertEqual(uniform_partitions(7), ((0,) * 7, tuple(range(7))))
        self.assertEqual(survey(l7(), 7, uniform=True), ([], 0))

    def test_report_restriction_field(self) -> None:
        """reports: --group-rep adds one restriction key after points; without it the v1 payload is unchanged."""
        reports, copies = survey(m3(), 4)
        plain = json.loads(survey_json(m3(), 4, reports, copies))
        self.assertEqual(list(plain),
                         ["format", "target", "points", "copies", "classes"])
        marked = json.loads(survey_json(m3(), 4, reports, copies, "uniform"))
        self.assertEqual(list(marked), ["format", "target", "points",
                                        "restriction", "copies", "classes"])
        self.assertEqual(marked["restriction"], "uniform")

    @unittest.skipUnless(os.environ.get("FLRP_EQSEARCH_SLOW") == "1",
                         "set FLRP_EQSEARCH_SLOW=1 for the Eq(10) uniform "
                         "sweep (about seven minutes)")
    def test_l7_eq10_uniform_committed_report(self) -> None:
        """uniform: the pure Eq(10) --group-rep sweep re-derives the committed ten-point report — zero uniform copies — byte for byte.  The committed file is the fast engine's 2026-07-24 output, so this pin is also a cross-engine parity check at ten points."""
        reports, copies = survey(l7(), 10, uniform=True)
        self.assertEqual((reports, copies), ([], 0))
        self.assertEqual(
            survey_json(l7(), 10, reports, copies, restriction="uniform"),
            (Path(__file__).parent / "out"
             / "l7_eq10_uniform_report.json").read_text())

    def test_cli_group_rep_end_to_end(self) -> None:
        """cli: --group-rep runs the M3 pilot claim on four points, marks stdout, and writes a report carrying the restriction field."""
        target = Path(__file__).parent / "inputs" / "v4_regular_m3.json"
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "report.json"
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                code = main(["eqsearch.py", str(target), "4", "--group-rep",
                             "--json", str(out)])
            self.assertEqual(code, 0)
            report = json.loads(out.read_text())
        self.assertEqual(report["restriction"], "uniform")
        self.assertEqual((report["target"], report["copies"]), ("M3", 6))
        self.assertEqual([c["closed"] for c in report["classes"]], [True])
        self.assertIn("M3 in Eq(4) (uniform copies only): 6 labelled copies",
                      stdout.getvalue())


class TargetLatticeTests(unittest.TestCase):

    def test_tables_from_leq_reproduces_m3(self) -> None:
        """targets: the M3 order matrix rebuilds the pilot's meet and join tables."""
        up = {0: {0, 1, 2, 3, 4}, 1: {1, 4}, 2: {2, 4}, 3: {3, 4}, 4: {4}}
        leq = tuple(tuple(y in up[x] for y in range(5)) for x in range(5))
        built = tables_from_leq("M3", leq)
        self.assertEqual((built.meet, built.join), (m3().meet, m3().join))

    def test_validate_target_finds_bounds(self) -> None:
        """targets: validation returns the bounds of a well-formed lattice."""
        self.assertEqual(validate_target(m3()), (0, 4))
        self.assertEqual(validate_target(l7()), (0, 6))

    def test_cli_rejects_malformed_arguments(self) -> None:
        """cli: wrong argument shapes are usage errors, never silent successes."""
        for argv in (["eqsearch.py"],
                     ["eqsearch.py", "t.json", "4", "--json"],
                     ["eqsearch.py", "t.json", "4", "--report", "x.json"],
                     ["eqsearch.py", "t.json", "4", "--json", "x.json", "y"],
                     ["eqsearch.py", "--group-rep"],
                     ["eqsearch.py", "t.json", "4", "--group-rep", "--json"]):
            with contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(main(argv), 2)

    def test_validate_target_rejects_broken_tables(self) -> None:
        """targets: a corrupted meet table fails lattice validation."""
        broken = TargetLattice(
            name="broken", size=5,
            meet=tuple(tuple(1 if (k, l) == (2, 3) else v
                             for l, v in enumerate(row))
                       for k, row in enumerate(m3().meet)),
            join=m3().join)
        with self.assertRaises(CertificateError):
            validate_target(broken)


class M3SearchTests(unittest.TestCase):
    """M3 on four points: the classical closed representation."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.reports, cls.copies = survey(m3(), 4)

    def test_m3_copy_census(self) -> None:
        """M3/Eq(4): 42 labelled copies in exactly two relabeling classes."""
        self.assertEqual(self.copies, 42)
        self.assertEqual([r.orbit_size for r in self.reports], [1, 6])

    def test_matchings_class_is_closed(self) -> None:
        """M3/Eq(4): the three-matchings class is closed — |G| = 4, |M| = 8, Inv = M3."""
        closed = [r for r in self.reports if r.closed]
        self.assertEqual(len(closed), 1)
        r = closed[0]
        self.assertEqual((r.orbit_size, r.group_order, r.monoid_size,
                          r.proper_maps, r.invariants),
                         (1, 4, 8, 0, 5))

    def test_mixed_class_is_not_closed(self) -> None:
        """M3/Eq(4): the two-matchings-plus-a-pair class fails closure."""
        open_ = [r for r in self.reports if not r.closed]
        self.assertEqual(len(open_), 1)
        self.assertGreater(open_[0].invariants, 5)

    def test_closed_class_round_trips_to_a_certificate(self) -> None:
        """loop: the closed class's witness algebra certifies Con ≅ M3 end to end."""
        report = next(r for r in self.reports if r.closed)
        alg = closed_class_algebra("M3", report, 4)
        self.assertEqual([op.table for op in alg.operations],
                         [[1, 0, 3, 2], [2, 3, 0, 1], [3, 2, 1, 0]])
        cert = build_certificate(alg, m3())
        check_certificate(alg, m3(), cert)
        claim = json.loads(claim_input("M3EqSearch", "2026-07-22", alg, m3()))
        self.assertEqual(claim["format"], "flrp-cert-input v1")
        self.assertEqual(claim["lattice"]["name"], "M3")

    def test_survey_json_is_deterministic(self) -> None:
        """reports: two runs of the same survey serialize byte-identically."""
        again, copies = survey(m3(), 4)
        self.assertEqual(survey_json(m3(), 4, self.reports, self.copies),
                         survey_json(m3(), 4, again, copies))


class L7SessionTests(unittest.TestCase):
    """The 2026-07-22 session results for `L7` (issue #484), reproduced."""

    def test_no_copies_below_six_points(self) -> None:
        """L7: Eq(4) and Eq(5) contain no sublattice copy at all."""
        for n in (4, 5):
            self.assertEqual(sublattice_copies(l7(), EqTables(n)), [])

    def test_eq6_census_and_closure(self) -> None:
        """L7/Eq(6): 1080 copies, two classes (rigid and symmetric), neither closed."""
        reports, copies = survey(l7(), 6)
        self.assertEqual(copies, 1080)
        self.assertEqual(
            sorted((r.orbit_size, r.group_order, r.monoid_size, r.proper_maps,
                    r.invariants, r.closed) for r in reports),
            [(360, 2, 8, 0, 31, False), (720, 1, 7, 0, 203, False)])

    @unittest.skipUnless(os.environ.get("FLRP_EQSEARCH_SLOW") == "1",
                         "set FLRP_EQSEARCH_SLOW=1 for the Eq(7) sweep")
    def test_eq7_census_and_closure(self) -> None:
        """L7/Eq(7): 55,440 copies, 12 classes, no proper maps anywhere, none closed."""
        reports, copies = survey(l7(), 7)
        self.assertEqual(copies, 55440)
        self.assertEqual(len(reports), 12)
        self.assertFalse(any(r.closed for r in reports))
        self.assertFalse(any(r.proper_maps for r in reports))
        self.assertEqual(sorted(r.invariants for r in reports),
                         [59, 59] + [877] * 10)
        self.assertEqual(sorted(r.group_order for r in reports),
                         [1] * 10 + [2, 2])
        # 7 is prime, so no class is all-uniform: the filter side of the
        # empty --group-rep census (UniformSweepTests degeneration test)
        self.assertFalse(any(all(is_uniform(p) for p in r.representative)
                             for r in reports))


class OrbitStabilizerClassifierTests(unittest.TestCase):
    """The orbit–stabilizer classifier of issue #499, pinned byte-identical to
    the materialized reference on every census where materialization is
    feasible.  This parity is what licenses trusting it at twelve points,
    where ``12! ≈ 4.8 × 10⁸`` puts the materialized classifier out of reach and
    only orbit–stabilizer can run."""

    def _parity(self, lat: TargetLattice, n: int, uniform: bool = False) -> None:
        eq = UniformTables(n) if uniform else EqTables(n)
        copies = sublattice_copies(lat, eq)
        self.assertEqual(_classify_orbit_stabilizer(copies, eq),
                         _classify_materialized(copies, eq))

    def test_setwise_stabilizer_spot_checks(self) -> None:
        """classifier: |Stab| of a lone |0,1|2,3| on four points is its block
        automorphism group (order 8, so orbit 4!/8 = 3, the three 2² partitions);
        the three matchings of M3 are stabilized setwise by all of S₄ (order 24,
        orbit 1) — the relation-permuting symmetry a rigid target never has."""
        self.assertEqual(_setwise_stabilizer_order([(0, 0, 2, 2)], 4), 8)
        self.assertEqual(
            _setwise_stabilizer_order(
                [(0, 1, 0, 1), (0, 1, 1, 0), (0, 0, 2, 2)], 4),
            24)

    def test_parity_m3_eq4(self) -> None:
        """classifier: orbit–stabilizer == materialized on M3/Eq(4)."""
        self._parity(m3(), 4)

    def test_parity_m3_eq6(self) -> None:
        """classifier: orbit–stabilizer == materialized on M3/Eq(6) — where the
        block-profile invariant alone merges distinct size-60 orbits and the
        isomorphism refinement is what separates them."""
        self._parity(m3(), 6)

    def test_parity_m3_eq6_uniform(self) -> None:
        """classifier: orbit–stabilizer == materialized on the M3/Eq(6) uniform pool."""
        self._parity(m3(), 6, uniform=True)

    def test_parity_l7_eq6(self) -> None:
        """classifier: orbit–stabilizer == materialized on L7/Eq(6) (rigid and symmetric classes)."""
        self._parity(l7(), 6)

    @unittest.skipUnless(os.environ.get("FLRP_EQSEARCH_SLOW") == "1",
                         "set FLRP_EQSEARCH_SLOW=1 for the L7/Eq(7) "
                         "classifier parity (about half a minute)")
    def test_parity_l7_eq7(self) -> None:
        """classifier: orbit–stabilizer == materialized on L7/Eq(7) — 55,440 copies, 12 classes."""
        self._parity(l7(), 7)


# ---------------------------------------------------------------------------
# A logging runner, matching test_flrp.py.

class LoggingResult(unittest.TextTestResult):
    """Prints each test's one-line docstring with a pass/fail mark."""

    @staticmethod
    def _describe(test: unittest.TestCase) -> str:
        return test.shortDescription() or test.id().rsplit(".", maxsplit=1)[-1]

    def addSuccess(self, test: unittest.TestCase) -> None:
        super().addSuccess(test)
        self.stream.writeln(f"✅ {self._describe(test)}")  # type: ignore[attr-defined]

    def addFailure(self, test: unittest.TestCase, err) -> None:  # type: ignore[no-untyped-def]
        super().addFailure(test, err)
        self.stream.writeln(f"❌ {self._describe(test)}")  # type: ignore[attr-defined]

    def addError(self, test: unittest.TestCase, err) -> None:  # type: ignore[no-untyped-def]
        super().addError(test, err)
        self.stream.writeln(f"❌ {self._describe(test)} (error)")  # type: ignore[attr-defined]


if __name__ == "__main__":
    unittest.main(
        testRunner=unittest.TextTestRunner(resultclass=LoggingResult, verbosity=0))
