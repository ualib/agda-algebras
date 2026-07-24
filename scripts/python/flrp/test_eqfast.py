"""Tests for the numpy backend (`make flrp-test`; skipped without numpy).

File: scripts/python/flrp/test_eqfast.py

Description:

  The contract under test is parity: the fast backend must produce the same
  partitions, the same tables, the same copies, the same classes, and — the
  strongest form — byte-identical survey reports wherever both backends run.

  On top of parity, the fast backend re-verifies the large censuses: the
  `Eq(7)` figures in seconds, and (behind ``FLRP_EQSEARCH_SLOW=1``) the
  `Eq(8)` sweep that settled the eight-point frontier for `L7`, whose report
  is committed at ``out/l7_eq8_report.json``.

Usage:

  python3 scripts/python/flrp/test_eqfast.py

  Or run ``make flrp-test`` from the top-level repo directory.  (Running the
  file directly is what puts ``scripts/python/flrp`` on ``sys.path`` for the
  flat sibling imports; the directory is deliberately not a package.)
"""

from __future__ import annotations

import os
import unittest
from collections import Counter
from pathlib import Path

try:
    import numpy  # noqa: F401  (probe only)
    HAVE_NUMPY = True
except ImportError:
    HAVE_NUMPY = False

if HAVE_NUMPY:
    from eqfast import FastTables, survey_fast
from eqsearch import EqTables, survey, survey_json
from test_eqsearch import l7
from test_flrp import m3

REPORT = Path(__file__).parent / "out" / "l7_eq8_report.json"


@unittest.skipUnless(HAVE_NUMPY, "numpy is not installed")
class FastBackendTests(unittest.TestCase):

    def test_tables_match_pure(self) -> None:
        """fast: vectorized meet and join tables equal the pure ones (n ≤ 5)."""
        for n in (4, 5):
            eq, ft = EqTables(n), FastTables(n)
            self.assertEqual(eq.parts, ft.parts)
            self.assertEqual(eq.meet, [list(map(int, row)) for row in ft.meet])
            self.assertEqual(eq.join, [list(map(int, row)) for row in ft.join])

    def test_m3_survey_parity(self) -> None:
        """fast: the M3/Eq(4) survey report is byte-identical to the pure one."""
        self.assertEqual(survey_json(m3(), 4, *survey(m3(), 4)),
                         survey_json(m3(), 4, *survey_fast(m3(), 4)))

    def test_l7_eq6_survey_parity(self) -> None:
        """fast: the L7/Eq(6) survey report is byte-identical to the pure one."""
        self.assertEqual(survey_json(l7(), 6, *survey(l7(), 6)),
                         survey_json(l7(), 6, *survey_fast(l7(), 6)))

    def test_l7_eq7_census(self) -> None:
        """fast: Eq(7) reproduces 55,440 copies in 12 classes, none closed."""
        reports, copies = survey_fast(l7(), 7)
        self.assertEqual(copies, 55440)
        self.assertEqual(len(reports), 12)
        self.assertFalse(any(r.closed for r in reports))
        self.assertEqual(sorted(r.invariants for r in reports),
                         [59, 59] + [877] * 10)

    @unittest.skipUnless(os.environ.get("FLRP_EQSEARCH_SLOW") == "1",
                         "set FLRP_EQSEARCH_SLOW=1 for the Eq(8) sweep (hours)")
    def test_l7_eq8_census_and_committed_report(self) -> None:
        """fast: Eq(8) — 4,112,640 copies, 108 classes, none closed — and the
        committed report is exactly this run's output."""
        reports, copies = survey_fast(l7(), 8)
        self.assertEqual(copies, 4112640)
        self.assertEqual(len(reports), 108)
        self.assertFalse(any(r.closed for r in reports))
        self.assertEqual(Counter(r.orbit_size for r in reports),
                         Counter({40320: 96, 20160: 12}))
        self.assertEqual(Counter(r.monoid_size for r in reports),
                         Counter({9: 89, 10: 16, 11: 2, 13: 1}))
        self.assertEqual(Counter(r.invariants for r in reports),
                         Counter({4140: 89, 164: 12, 864: 4,
                                  337: 1, 131: 1, 50: 1}))
        self.assertEqual(survey_json(l7(), 8, reports, copies),
                         REPORT.read_text())


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
