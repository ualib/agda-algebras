"""Tests for the GAP interval → lattice bridge (`make flrp-test`).

GAP-free by design: the raw artifacts are built inline (the bridge never runs
GAP), so this suite pins the Python half of issue #487 without the engine.

Three things are checked:

+ the lattice construction and the isomorphism test — the pentagon interval's
  order matrix builds N5 and matches N5 but not M3;
+ the direct-certificate route end to end without Agda — the regular V4 coset
  action (four points, two unary generators) flows through `claim_from_coset`
  and `lattice.build_certificate` to a whole-lattice certificate for M3, the
  same algebra the pilot `FLRP.Certificates.Pilot.V4RegularM3` certifies; and
+ the guard rails — a wrong `format` is rejected, and a coset index past the
  emitter's Fin-literal cap refuses to emit a claim (it is bridge-route work).
"""

from __future__ import annotations

import unittest
from typing import Dict, List

from cg2 import Algebra, CertificateError, Operation
from eqsearch import tables_from_leq
from gap_interval import (canonical_artifact, claim_from_coset,
                          interval_lattice, lattice_iso, load_raw)
from lattice import build_certificate

# Reflexive order matrices (leq[i][j] = "i <= j") for the two nondistributive
# five-element lattices, in the canonical 0 = bottom, 4 = top labeling.
N5_LEQ = [[True,  True,  True,  True,  True],   # 0 < 1 < 3 < 4 and 0 < 2 < 4
          [False, True,  False, True,  True],
          [False, False, True,  False, True],
          [False, False, False, True,  True],
          [False, False, False, False, True]]

M3_LEQ = [[True,  True,  True,  True,  True],   # 0 < 1, 2, 3 < 4 (diamond)
          [False, True,  False, False, True],
          [False, False, True,  False, True],
          [False, False, False, True,  True],
          [False, False, False, False, True]]


def raw_with(leq: List[List[bool]], coset: Dict[str, object]) -> dict:
    """A minimal raw interval artifact carrying `leq` and a coset action."""
    size = len(leq)
    return {
        "format": "flrp-gap-interval-raw v1",
        "engine": {"gap": "test", "libraries": {}},
        "group": {"source": "SmallGroup", "id": [4, 2], "order": 4,
                  "structureDescription": "C2 x C2"},
        "subgroup": {"order": 1, "index": coset["points"], "coreFree": True,
                     "coreOrder": 1, "generators": "[  ]"},
        "interval": {"size": size, "covers": [], "leq": leq, "nodes": []},
        "cosetAction": coset,
    }


# The regular action of V4 on its four elements: left multiplication by the two
# generators a and b (points e, a, b, ab = 0, 1, 2, 3).  Con of this algebra is
# M3, and [1, V4] = Sub(V4) = M3, so the interval lattice here is M3 too.
V4_COSET = {
    "points": 4, "directCertifiable": True,
    "generators": [
        {"name": "g0", "arity": 1, "table": [1, 0, 3, 2]},   # x -> a·x
        {"name": "g1", "arity": 1, "table": [2, 3, 0, 1]},   # x -> b·x
    ],
}


class TestLatticeAndIso(unittest.TestCase):

    def test_interval_lattice_builds_n5(self) -> None:
        """interval_lattice turns the pentagon order matrix into an N5 lattice."""
        lat = interval_lattice(raw_with(N5_LEQ, V4_COSET))
        self.assertEqual(lat.size, 5)
        # bottom 0 absorbs under meet, top 4 absorbs under join.
        self.assertTrue(all(lat.meet[0][l] == 0 for l in range(5)))
        self.assertTrue(all(lat.join[4][l] == 4 for l in range(5)))
        # 1 and 2 are incomparable: their meet is bottom, their join is top.
        self.assertEqual(lat.meet[1][2], 0)
        self.assertEqual(lat.join[1][2], 4)

    def test_iso_matches_n5_not_m3(self) -> None:
        """lattice_iso identifies N5 with N5 and separates it from M3."""
        n5 = tables_from_leq("N5", N5_LEQ)
        m3 = tables_from_leq("M3", M3_LEQ)
        self.assertIsNotNone(lattice_iso(n5, n5))
        self.assertIsNone(lattice_iso(n5, m3))
        self.assertIsNone(lattice_iso(m3, n5))


class TestDirectCertificateRoute(unittest.TestCase):

    def test_v4_coset_certifies_m3(self) -> None:
        """The V4 coset tables flow through a claim to an M3 certificate."""
        raw = raw_with(M3_LEQ, V4_COSET)
        lat = interval_lattice(raw)                       # M3
        claim = claim_from_coset(raw, lat, "V4RegularM3Gap",
                                 "FLRP.Certificates.Group", "2026-07-24", "")
        self.assertEqual(claim["format"], "flrp-cert-input v1")
        self.assertEqual(claim["algebra"]["card"], 4)
        self.assertEqual(len(claim["algebra"]["operations"]), 2)
        # Rebuild the algebra from the claim and certify Con ≅ M3 engine-side.
        alg = Algebra(
            name=claim["algebra"]["name"], card=claim["algebra"]["card"],
            operations=tuple(Operation(op["name"], op["arity"], op["table"])
                             for op in claim["algebra"]["operations"]))
        cert = build_certificate(alg, lat)
        self.assertEqual(len(cert.parts), 5)              # M3 has five congruences

    def test_big_index_refuses_claim(self) -> None:
        """An index past the Fin-literal cap is bridge-route work, not direct."""
        big = dict(V4_COSET, points=36, directCertifiable=False)
        raw = raw_with(N5_LEQ, big)
        with self.assertRaises(CertificateError):
            claim_from_coset(raw, interval_lattice(raw), "X",
                             "FLRP.Certificates.Group", "2026-07-24", "")


class TestGuardRails(unittest.TestCase):

    def test_load_raw_rejects_bad_format(self) -> None:
        """load_raw refuses anything that is not a raw interval artifact."""
        import json
        import tempfile
        from pathlib import Path
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "x.json"
            p.write_text(json.dumps({"format": "nope"}))
            with self.assertRaises(CertificateError):
                load_raw(p)

    def test_canonical_artifact_shape(self) -> None:
        """canonical_artifact carries the match verdict and the coset action."""
        raw = raw_with(N5_LEQ, V4_COSET)
        lat = interval_lattice(raw)
        n5 = tables_from_leq("N5", N5_LEQ)
        art = canonical_artifact(raw, lat, n5, lattice_iso(lat, n5), "2026-07-24")
        self.assertEqual(art["format"], "flrp-gap-interval v1")
        self.assertTrue(art["match"]["isomorphic"])
        self.assertIn("meet", art["interval"])
        self.assertIn("cosetAction", art)


# A logging runner, matching test_flrp.py / test_eqsearch.py.

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
