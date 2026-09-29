"""Tests for the eight-element lattice census (`make flrp-test`).

File: scripts/python/flrp/test_lattices8.py

Pinned here:

+ the enumerator reproduces the number of lattices with n elements up to
  isomorphism for n ≤ 8 (OEIS A006966: 1, 1, 1, 2, 5, 15, 53, 222);
+ the census reproduces the counts of Kjos-Hanssen's note on the eight-element
  congruence lattices (15 distributive, 96 adjoined ordinal sums, 69 with a
  disconnected proper part, 168 of at least one kind, 54 of none), and its
  54 lattices of no kind are exactly the 54 of the note's Table 1, matched
  lattice for lattice through the transcribed cover lists;
+ the split of the 69: 8 are Snow parallel sums (two components, each an
  interval), 61 are not, the 61 are closed under duality, and 14 of them
  are simple lattices;
+ P(2x2,2x2) and its dual (the RP-3 target stanzas pm2m2 and pm2m2d) are
  among the 61 and are simple;
+ the committed census record and the committed stanzas re-derive byte for
  byte (the golden discipline shared with the SLR catalog).
"""

from __future__ import annotations

import json
import unittest
from pathlib import Path

from eqsearch import parse_target
from gap_interval import lattice_iso
from lattice import TargetLattice
from lattices8 import (KNOWN_COUNTS, OUT_JSON, STANZA_DIR, census, census_json,
                       enumerate_lattices, stanza, summary, unsupported)


class Lattices8Tests(unittest.TestCase):

    @classmethod
    def setUpClass(cls) -> None:
        cls.lattices = enumerate_lattices(8)
        cls.records = census(8)
        cls.counts = summary(cls.records)

    def test_lattice_counts(self) -> None:
        """The enumerator reproduces OEIS A006966 up to eight elements."""
        for n, expected in KNOWN_COUNTS.items():
            self.assertEqual(len(enumerate_lattices(n)), expected, n)

    def test_kjos_hanssen_counts(self) -> None:
        """The note's counts of the three formal kinds and of the rest."""
        c = self.counts
        self.assertEqual(c["lattices"], 222)
        self.assertEqual(c["distributive"], 15)
        self.assertEqual(c["adjoined ordinal sums"], 96)
        self.assertEqual(c["disconnected proper part (the note's parallel sums)"], 69)
        self.assertEqual(c["of at least one kind"], 168)
        self.assertEqual(c["of no kind"], 54)

    def test_table1_is_the_no_kind_class(self) -> None:
        """Every lattice of no kind is in Table 1 and conversely."""
        for r in self.records:
            no_kind = not (r.distributive or r.adjoined_ordinal_sum or r.disconnected)
            self.assertEqual(no_kind, r.kjos_hanssen is not None, r.covers)
        self.assertEqual(self.counts["in Table 1"], 54)
        # The dual column of Table 1 agrees with the census's duals.
        by_number = {r.kjos_hanssen: r for r in self.records if r.kjos_hanssen is not None}
        for r in by_number.values():
            dual = self.records[r.dual_index - 1]
            self.assertIsNotNone(dual.kjos_hanssen)

    def test_the_split_of_the_parallel_sums(self) -> None:
        """Snow's lemma covers 8 of the 69; the other 61 are closed under
        duality and contain 14 simple lattices."""
        c = self.counts
        self.assertEqual(c["Snow parallel sums (two interval components)"], 8)
        uns = unsupported(self.records)
        self.assertEqual(len(uns), 61)
        indices = {r.index for r in uns}
        for r in uns:
            self.assertIn(r.dual_index, indices)
        self.assertEqual(c["simple lattices"], 15)
        self.assertEqual(c["simple and unsupported"], 14)
        # Every Snow sum has exactly two components, each an interval.
        for r in self.records:
            if r.snow_sum:
                self.assertEqual(len(r.components), 2)
                self.assertTrue(all(m == 1 and x == 1 for _s, m, x in r.components))

    def test_pm2m2_is_unsupported_and_simple(self) -> None:
        """The two RP-3 eight-element targets are among the 61 and simple."""
        uns = {r.index: r for r in unsupported(self.records)}
        for stem in ("pm2m2", "pm2m2d"):
            target = parse_target(Path("scripts/gap/flrp/inputs") / f"{stem}.json")
            hits = [r for r in uns.values()
                    if lattice_iso(target, TargetLattice(**stanza(r, self.lattices[r.index - 1]))) is not None]
            self.assertEqual(len(hits), 1, stem)
            self.assertTrue(hits[0].simple, stem)

    def test_committed_record_rederives(self) -> None:
        """The census JSON and the stanzas under inputs/lat8 are current."""
        self.assertEqual(OUT_JSON.read_text(), census_json(self.records))
        committed = sorted(STANZA_DIR.glob("l8_*.json"))
        self.assertEqual(len(committed), 61)
        for r in unsupported(self.records):
            path = STANZA_DIR / f"l8_{r.index}.json"
            self.assertEqual(json.loads(path.read_text()), stanza(r, self.lattices[r.index - 1]))


if __name__ == "__main__":
    unittest.main()
