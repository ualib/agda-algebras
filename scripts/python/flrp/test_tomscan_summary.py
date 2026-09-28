"""Tests for the tables-of-marks scan summarizer (`make flrp-test`).

File: scripts/python/flrp/test_tomscan_summary.py

GAP-free by design: the summarizer is a pure transcription of a text log.
Three things are checked, on a fixture that reproduces GAP's line wrapping
and a real line of each kind from the 2026-09-28 hexagon run:

+ unwrapping joins a wrapped record back together and drops the banner;
+ every record kind parses into its fields, timings are not recorded, and a
  line of an unknown shape lands in `unparsed` rather than being dropped;
+ the record renders deterministically, and the up-set list of a committed
  stanza is the one the engine expects (1-based, bottom first).
"""

from __future__ import annotations

import json
import unittest
from pathlib import Path

from tomscan_summary import (Tally, gap_list, parse_record, record, render,
                             summarize, unwrap, upsets)

FIXTURE = """\
🧮 agda-algebras GAP shell (issue #487)
   GAP      : 4.15.1
   libraries: smallgrp / transgrp / primgrp  (packageSet=standard)
engine GAP 4.15.1 tomlib 1.2.11
HIT U4(2) |G|=25920 class 66 |H|=24 index 1080 interval orders [ 24, 96, 216, 648, 960, 25920
 ]
AMBIGUOUS L2(7).2 |G|=336 class 14 |H|=8 index 42 multiplicities [ 1, 2, 1, 1
 ]
UNRESOLVED (|G| = 44352000 above FLRP_RESOLVE_BOUND) HS class 511
EXPLICIT L2(7).2 class 14: |G| = 336 |H| = 8 (D8) index 42 core-free true; interval size 6 orders [ 16, 24, 24, 168 ] covers [ [ 0, 1 ], [ 0, 2 ], [ 0, 3 ], [ 1, 5 ], [ 2, 4 ], [ 3, 4 ], [ 4, 5 ] ]; target: false (44 ms)
EXPLICIT Sz(8) class 6: |G| = 29120 |H| = 7 (C7) index 4160 core-free true; interval size 7 orders [ 14, 56, 56, 448, 448
 ] covers [ [ 0, 1 ], [ 0, 2 ], [ 0, 3 ], [ 1, 6 ], [ 2, 4 ], [ 3, 5 ], [ 4, 6 ], [ 5, 6 ] ]; target: true (185 ms)
scanned 414 tables; size-6 upper intervals: 4810; marks-exact hits: 16; ambiguous survivors: 143
HIT-LIKE junk that is not a record
"""


class TomscanSummaryTests(unittest.TestCase):

    def lines(self):
        return FIXTURE.splitlines()

    def test_unwrap_joins_wrapped_records_and_drops_the_banner(self) -> None:
        """A record wrapped over two physical lines is one record; the banner is not."""
        records = unwrap(self.lines())
        self.assertEqual(len(records), 7)
        self.assertTrue(records[0].startswith("HIT U4(2)"))
        self.assertIn("25920 ]", records[0])
        self.assertFalse(any(r.startswith(("GAP", "engine")) for r in records))

    def test_each_kind_parses(self) -> None:
        """Every record kind yields its fields; timings are not part of the record."""
        s = summarize(self.lines())
        self.assertEqual((s.gapVersion, s.tomlibVersion), ("4.15.1", "1.2.11"))
        self.assertEqual(s.tally, Tally(414, 6, 4810, 16, 143))
        self.assertEqual(len(s.hits), 1)
        self.assertEqual(s.hits[0].table, "U4(2)")
        self.assertEqual(s.hits[0].intervalOrders, (24, 96, 216, 648, 960, 25920))
        self.assertEqual(s.hits[0].index, 1080)
        self.assertEqual(len(s.ambiguous), 1)
        self.assertEqual(s.ambiguous[0].cls, 14)
        self.assertEqual(len(s.unresolved), 1)
        self.assertEqual((s.unresolved[0].table, s.unresolved[0].order), ("HS", 44352000))
        self.assertEqual(len(s.explicit), 2)
        e0, e1 = s.explicit
        self.assertEqual((e0.structure, e0.coreFree, e0.target), ("D8", True, False))
        self.assertEqual((e1.table, e1.structure, e1.target), ("Sz(8)", "C7", True))
        self.assertEqual(e1.intervalOrders, (14, 56, 56, 448, 448))
        self.assertEqual(s.unparsed, ("HIT-LIKE junk that is not a record",))

    def test_unknown_shape_is_reported_not_dropped(self) -> None:
        kind, value = parse_record("HIT with nothing after it")
        self.assertEqual(kind, "unparsed")
        self.assertEqual(value, "HIT with nothing after it")

    def test_render_is_deterministic_and_records_no_timing(self) -> None:
        s = summarize(self.lines())
        rec = record(s, None, "2026-09-28", {"tables": "all", "resolveBound": "default"})
        text = render(rec)
        self.assertEqual(text, render(json.loads(text)))
        self.assertNotIn(" ms", text)
        self.assertEqual(json.loads(text)["format"], "flrp-tomscan v1")

    def test_upsets_of_the_hexagon_stanza(self) -> None:
        """The committed P(3,3) stanza's up-sets, 1-based, bottom first."""
        stanza = Path("scripts/gap/flrp/inputs/p33.json")
        if not stanza.exists():
            self.skipTest("run from the repository root")
        rows = upsets(stanza)
        self.assertEqual(rows, [[1, 2, 3, 4, 5, 6], [2, 3, 6], [3, 6], [4, 5, 6], [5, 6], [6]])
        self.assertEqual(gap_list(rows), "[[1,2,3,4,5,6],[2,3,6],[3,6],[4,5,6],[5,6],[6]]")


if __name__ == "__main__":
    unittest.main()
