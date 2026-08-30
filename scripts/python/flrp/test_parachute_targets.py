"""Tests for the RP-3 parachute target stanzas (`make flrp-test`).

File: scripts/python/flrp/test_parachute_targets.py

GAP-free by design: the stanzas are pure functions of the cover lists in
`parachute_targets.py`.  Three things are checked:

+ the committed stanzas under scripts/gap/flrp/inputs/ re-derive byte for
  byte (the golden discipline shared with the SLR catalog);
+ every target parses back as a valid bounded lattice through the canonical
  `parse_target`, and the four targets have the intended sizes and atom
  counts (two big canopies, plus the extra two-chain canopy of P(3,3,2));
+ the three seven-element targets are pairwise non-isomorphic, so a sweep
  confirmation against one of them says nothing accidental about another.
"""

from __future__ import annotations

import unittest

from eqsearch import parse_target
from gap_interval import lattice_iso
from parachute_targets import TARGETS, check_stanzas, leq_from_covers, stanza_path


class ParachuteTargetTests(unittest.TestCase):

    def test_committed_stanzas_rederive(self) -> None:
        """The committed target stanzas re-derive byte for byte."""
        self.assertEqual(list(check_stanzas()), [])

    def test_targets_parse_and_have_expected_shape(self) -> None:
        """Every target parses as a bounded lattice with the intended size and atom count."""
        atoms = {"p33": 2, "p332": 3, "p34": 2, "p3m2": 2}
        for spec in TARGETS:
            lat = parse_target(stanza_path(spec))
            self.assertEqual(lat.size, spec.size)
            self.assertEqual(
                sum(1 for lo, _ in spec.covers if lo == 0), atoms[spec.stem])
            leq = leq_from_covers(spec)
            self.assertTrue(all(leq[0][y] for y in range(spec.size)))

    def test_seven_element_targets_pairwise_distinct(self) -> None:
        """The three seven-element targets are pairwise non-isomorphic."""
        sevens = [parse_target(stanza_path(s)) for s in TARGETS if s.size == 7]
        self.assertEqual(len(sevens), 3)
        for i in range(len(sevens)):
            for j in range(i + 1, len(sevens)):
                self.assertIsNone(lattice_iso(sevens[i], sevens[j]))


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
