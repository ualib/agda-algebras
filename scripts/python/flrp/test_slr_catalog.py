"""Tests for the SmallLatticeReps catalog transcription (`make flrp-test`).

File: scripts/python/flrp/test_slr_catalog.py

Description:

  Guards the transcription stage of issue #485 (``slr_catalog.py``):

  + shape pins — entry count, carrier sizes, lattice sizes, and the
    renderable/deferred/parked/erratum split, all against the § 6 catalog as
    read during the 2026-07-22 transcription session;
  + identification pins — manuscript L1 is N5 (tables written out by hand),
    manuscript L2 is the pilot's M3 byte for byte, and manuscript L10 is this
    library's L7 under exactly one relabeling, the one documented in
    ``docs/notes/flrp-slr-naming.md``;
  + the B28 erratum — Con(B28) as printed has eight congruences, each
    re-verified against the operation tables independently of cg2;
  + parser guard rails — synthetic tikz/array fragments with an unorientable
    edge, a non-cover edge, a non-lattice order, or a malformed value table
    must all fail loudly;
  + the golden sweep — every committed artifact (claim files, lattice
    stanzas, audit JSONs, emitted modules) re-derives from the manuscript
    byte for byte.
"""

from __future__ import annotations

import json
import unittest
from itertools import permutations
from typing import Dict, Tuple

from cg2 import CertificateError
from eqsearch import parse_target
from lattice import congruence_lattice
from slr_catalog import (AKA, ERRATA, PARKED, REPO_ROOT, CatalogEntry,
                         certifiable, check_committed, input_path,
                         parse_catalog, parse_entry, renderable,
                         respects_operations)
from test_flrp import LoggingResult

CATALOG: Tuple[CatalogEntry, ...] = parse_catalog()
BY_NUMBER: Dict[int, CatalogEntry] = {entry.number: entry for entry in CATALOG}

PILOT_INPUT = REPO_ROOT / "scripts" / "python" / "flrp" / "inputs" / "v4_regular_m3.json"
L7_TABLES = REPO_ROOT / "scripts" / "python" / "flrp" / "inputs" / "l7_lattice.json"

# Carrier sizes of the printed algebras, § 6 of the 2016-06-10 draft.
CARDS: Dict[int, int] = {
    1: 4, 2: 3, 3: 7, 4: 4, 5: 12, 6: 6, 7: 6, 8: 6, 9: 16, 12: 9, 13: 19,
    15: 4, 17: 12, 19: 8, 21: 9, 23: 6, 24: 4, 25: 5, 26: 6, 27: 16, 28: 16,
    29: 5, 30: 5, 31: 5, 32: 5, 33: 16, 34: 4, 35: 4,
}

# Batch 1 of #485: unary, carrier ≤ 10, within the v1 renderer's 0F–9F range.
BATCH_1 = {1, 2, 3, 4, 6, 7, 8, 12, 15, 19, 21, 23, 24, 25, 26,
           29, 30, 31, 32, 34, 35}

# Batch 2 of #485: explicit tables past the 0F–9F range (B28 fell out of the
# original list as a candidate erratum).
BATCH_2 = {5, 9, 13, 17, 27, 33}


class CatalogShapeTests(unittest.TestCase):

    def test_catalog_shape(self) -> None:
        """catalog: 35 entries in manuscript order; algebras, parked set, and erratum set as expected."""
        self.assertEqual([entry.number for entry in CATALOG], list(range(1, 36)))
        with_algebra = {entry.number for entry in CATALOG if entry.algebra}
        self.assertEqual(with_algebra, set(CARDS))
        self.assertEqual({entry.number for entry in CATALOG if entry.algebra is None},
                         set(PARKED))
        self.assertEqual(set(ERRATA), {28})

    def test_carrier_sizes(self) -> None:
        """catalog: every printed algebra has the carrier size read in the transcription session."""
        for number, card in CARDS.items():
            algebra = BY_NUMBER[number].algebra
            assert algebra is not None
            self.assertEqual(algebra.card, card, f"B{number}")

    def test_lattice_sizes(self) -> None:
        """catalog: lattice sizes run 5, 5, then 6 through L8, then 7 (the manuscript's ≤ 7 census)."""
        for entry in CATALOG:
            expected = 5 if entry.number <= 2 else 6 if entry.number <= 8 else 7
            self.assertEqual(entry.lattice.size, expected, f"L{entry.number}")

    def test_renderable_split(self) -> None:
        """catalog: the renderable/deferred split is exactly the #485 batch-1/batch-2 split."""
        certified = {entry.number for entry in CATALOG
                     if certifiable(entry) and renderable(entry)}
        deferred = {entry.number for entry in CATALOG
                    if certifiable(entry) and not renderable(entry)}
        self.assertEqual(certified, BATCH_1)
        self.assertEqual(deferred, BATCH_2)


class IdentificationTests(unittest.TestCase):

    def test_l1_is_n5(self) -> None:
        """naming: manuscript L1 is the pentagon N5 (tables pinned by hand)."""
        lattice = BY_NUMBER[1].lattice
        self.assertEqual(lattice.meet, ((0, 0, 0, 0, 0), (0, 1, 0, 1, 1),
                                        (0, 0, 2, 0, 2), (0, 1, 0, 3, 3),
                                        (0, 1, 2, 3, 4)))
        self.assertEqual(lattice.join, ((0, 1, 2, 3, 4), (1, 1, 4, 3, 4),
                                        (2, 4, 2, 4, 4), (3, 3, 4, 3, 4),
                                        (4, 4, 4, 4, 4)))
        self.assertEqual(AKA[1], "N5")

    def test_l2_is_the_pilot_m3(self) -> None:
        """naming: manuscript L2's derived tables equal the pilot's M3 tables exactly."""
        pilot = json.loads(PILOT_INPUT.read_text())["lattice"]
        lattice = BY_NUMBER[2].lattice
        self.assertEqual([list(row) for row in lattice.meet], pilot["meet"])
        self.assertEqual([list(row) for row in lattice.join], pilot["join"])

    def test_l10_is_library_l7(self) -> None:
        """naming: manuscript L10 is library L7 under exactly one relabeling, the documented one."""
        stanza = json.loads(L7_TABLES.read_text())
        stanza = stanza.get("lattice", stanza)
        lib_meet = [list(row) for row in stanza["meet"]]
        lib_join = [list(row) for row in stanza["join"]]
        manuscript = BY_NUMBER[10].lattice

        def is_iso(sigma: Tuple[int, ...]) -> bool:
            return all(lib_meet[sigma[x]][sigma[y]] == sigma[manuscript.meet[x][y]]
                       and lib_join[sigma[x]][sigma[y]] == sigma[manuscript.join[x][y]]
                       for x in range(7) for y in range(7))

        isos = [sigma for sigma in permutations(range(7)) if is_iso(sigma)]
        self.assertEqual(isos, [(0, 2, 1, 3, 5, 4, 6)])

    def test_b2_is_the_shrunken_identity_algebra(self) -> None:
        """catalog: this draft's B2 is the 3-element identity algebra, not the pilot's V4 action."""
        algebra = BY_NUMBER[2].algebra
        assert algebra is not None
        self.assertEqual(algebra.card, 3)
        self.assertEqual([op.table for op in algebra.operations], [[0, 1, 2]])


class ErratumTests(unittest.TestCase):

    def test_b28_has_eight_congruences(self) -> None:
        """erratum: Con(B28) as printed has 8 congruences, each verified independently of cg2."""
        algebra = BY_NUMBER[28].algebra
        assert algebra is not None
        parts, _, _ = congruence_lattice(algebra)
        self.assertEqual(len(parts), 8)
        self.assertEqual(len(set(parts)), 8)
        for parent in parts:
            self.assertTrue(respects_operations(parent, algebra))
        self.assertEqual(BY_NUMBER[28].lattice.size, 7)


DIAMOND = """
\\node(0) at (0,-1)[e]{};
\\node(1) at (-1,0)[e]{};
\\node(2) at (1,0)[e]{};
\\node(3) at (0,1)[e]{};
\\draw(0)--(1);
\\draw(0)--(2);
\\draw(1)--(3);
\\draw(2)--(3);
"""

TWO_CHAIN = """
\\node(0) at (0,0)[e]{};
\\node(1) at (0,1)[e]{};
\\draw(0)--(1);
"""


class GuardRailTests(unittest.TestCase):

    def test_equal_height_edge_is_rejected(self) -> None:
        """guards: an edge between nodes at equal height cannot be oriented and is rejected."""
        with self.assertRaises(CertificateError):
            parse_entry(1, DIAMOND + "\\draw(1)--(2);\n")

    def test_non_cover_edge_is_rejected(self) -> None:
        """guards: a drawn edge implied by two others violates Hasse discipline and is rejected."""
        with self.assertRaises(CertificateError):
            parse_entry(1, DIAMOND + "\\draw(0)--(3);\n")

    def test_non_lattice_order_is_rejected(self) -> None:
        """guards: a bounded order without unique joins is rejected by the table derivation."""
        chunk = """
\\node(0) at (0,-2)[e]{};
\\node(1) at (-1,-1)[e]{};
\\node(2) at (1,-1)[e]{};
\\node(3) at (-1,1)[e]{};
\\node(4) at (1,1)[e]{};
\\node(5) at (0,2)[e]{};
\\draw(0)--(1);
\\draw(0)--(2);
\\draw(1)--(3);
\\draw(1)--(4);
\\draw(2)--(3);
\\draw(2)--(4);
\\draw(3)--(5);
\\draw(4)--(5);
"""
        with self.assertRaises(CertificateError):
            parse_entry(1, chunk)

    def test_wrong_table_header_is_rejected(self) -> None:
        """guards: a value table naming the wrong algebra number is rejected."""
        with self.assertRaises(CertificateError):
            parse_entry(1, TWO_CHAIN +
                        "$\\begin{array}{c|cc}\\bB_2& 0& 1\\\\\\hline f(x)& 0& 1\\end{array}$")

    def test_short_operation_row_is_rejected(self) -> None:
        """guards: an operation row shorter than the carrier is rejected."""
        with self.assertRaises(CertificateError):
            parse_entry(1, TWO_CHAIN +
                        "$\\begin{array}{c|cc}\\bB_1& 0& 1\\\\\\hline f(x)& 0\\end{array}$")


class GoldenTests(unittest.TestCase):

    def test_committed_artifacts_are_current(self) -> None:
        """golden: every committed input, audit JSON, and module re-derives from the manuscript byte for byte."""
        self.assertEqual(check_committed(CATALOG), [])

    def test_lattice_stanzas_are_eqsearch_targets(self) -> None:
        """golden: every bare lattice stanza parses as an eqsearch target."""
        for entry in CATALOG:
            if not certifiable(entry):
                lattice = parse_target(input_path(entry))
                self.assertEqual(lattice.size, entry.lattice.size)


if __name__ == "__main__":
    unittest.main(
        testRunner=unittest.TextTestRunner(resultclass=LoggingResult, verbosity=0))
