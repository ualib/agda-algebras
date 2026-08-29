"""Tests for the A5 filter-ideal certificate emitter (`make flrp-test`).

File: scripts/python/flrp/test_filter_ideal_certs.py

Description:

  Guards the generated module of issue #530: the committed
  ``src/FLRP/Certificates/FilterIdeal/A5Data.lagda.md`` must re-derive byte
  for byte from ``filter_ideal_certs.build_all()``, so the emitter and its
  committed output cannot drift apart silently — the same golden discipline
  as ``test_slr_catalog``'s committed-artifact sweep.  The internal
  consistency checks (interval facts, L16 tables, escalation certificates)
  run as part of ``build_all`` itself, so a passing golden test also
  re-verifies them.
"""

from __future__ import annotations

import unittest

from filter_ideal_certs import DEFAULT_OUTPUT, build_all
from test_flrp import LoggingResult


class TestA5DataGolden(unittest.TestCase):

    def test_committed_module_rederives_byte_for_byte(self) -> None:
        """golden: the committed A5Data module equals build_all() exactly."""
        committed = DEFAULT_OUTPUT.read_text(encoding="utf-8")
        self.assertEqual(build_all(), committed)


if __name__ == "__main__":
    unittest.main(
        testRunner=unittest.TextTestRunner(resultclass=LoggingResult, verbosity=0))
