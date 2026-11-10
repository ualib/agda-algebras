"""
File: scripts/python/certificates/test_unary_lattice_cert.py

Description: Tests for the whole-lattice certificate generator
  (`make certificates-test`).

  Four things are checked:

  + the partition primitives: normal form, forest edges, and meets;
  + the congruence lattice, against an independent oracle: for small unary
    algebras, the generator's congruences are exactly the compatible
    equivalence relations found by brute force over all set partitions, and
    for the cyclic algebras they are the congruences modulo the divisors;
  + the certificate, replayed engine-side, including controls: a certificate
    with one table entry or one trace entry changed fails the replay;
  + the golden round trip: regenerating reproduces the committed benchmark
    module byte for byte.

  The replay mirrors the Agda checker as a tripwire only; the Agda module
  remains the sole authority.
"""

from __future__ import annotations

import unittest
from dataclasses import replace
from math import gcd
from typing import FrozenSet, Iterator, List, Tuple

from unary_lattice_cert import (DEFAULT_OUT, Merge, Parts, Seed, Translate,
                                UnaryAlgebra, all_congruences, certificate,
                                cyclic_algebra, forest_edges, generate,
                                generated, meet_partition, normal_form,
                                verify_certificate)

from _utils.file_ops import read_text


def set_partitions(n: int) -> Iterator[Tuple[int, ...]]:
    """Every partition of {0, ..., n-1}, as restricted-growth label strings."""
    def extend(prefix: Tuple[int, ...]) -> Iterator[Tuple[int, ...]]:
        if len(prefix) == n:
            yield prefix
            return
        top = max(prefix, default=-1)
        for label in range(top + 2):
            yield from extend(prefix + (label,))
    return extend(())


def brute_force_congruences(alg: UnaryAlgebra) -> FrozenSet[Parts]:
    """The compatible equivalence relations, by enumeration of all partitions."""
    def compatible(labels: Tuple[int, ...]) -> bool:
        return all(labels[t[i]] == labels[t[j]]
                   for t in alg.tables
                   for i in range(alg.size) for j in range(alg.size)
                   if labels[i] == labels[j])
    return frozenset(normal_form(p) for p in set_partitions(alg.size)
                     if compatible(p))


# A unary algebra with two operations that is not a group action: a
# permutation and a non-injective map, on six points.
TWO_OPS: UnaryAlgebra = UnaryAlgebra(6, ((1, 0, 3, 2, 5, 4), (0, 0, 2, 2, 4, 4)))


class Partitions(unittest.TestCase):

    def test_normal_form(self) -> None:
        """Normal form points every index at the least member of its block."""
        self.assertEqual(normal_form(("a", "b", "a", "c", "b")), (0, 1, 0, 3, 1))

    def test_forest_edges(self) -> None:
        """Forest edges are the non-roots with their roots, in index order."""
        self.assertEqual(forest_edges((0, 1, 0, 3, 1)), ((2, 0), (4, 1)))

    def test_meet(self) -> None:
        """The meet of two partitions is their intersection."""
        self.assertEqual(meet_partition((0, 0, 0, 3), (0, 1, 0, 1)), (0, 1, 0, 3))


class Lattice(unittest.TestCase):

    def test_against_brute_force(self) -> None:
        """For small algebras the congruences are the brute-force ones."""
        for alg in (cyclic_algebra(6), cyclic_algebra(8), TWO_OPS):
            with self.subTest(size=alg.size, ops=len(alg.tables)):
                self.assertEqual(frozenset(all_congruences(alg)),
                                 brute_force_congruences(alg))

    def test_cyclic_divisors(self) -> None:
        """The congruences of the cyclic algebra of order 30 are mod d, d | 30."""
        n = 30
        expected = frozenset(normal_form(tuple(i % d for i in range(n)))
                             for d in range(1, n + 1) if n % d == 0)
        found = all_congruences(cyclic_algebra(n))
        self.assertEqual(len(found), 8)
        self.assertEqual(frozenset(found), expected)
        self.assertEqual(found[0], tuple(range(n)))

    def test_cyclic_principal(self) -> None:
        """Cg(i, j) in the cyclic algebra of order 30 is mod gcd(j - i, 30)."""
        n = 30
        for i, j in ((0, 1), (3, 9), (4, 19), (7, 7), (29, 5)):
            d = gcd(j - i, n) if i != j else n
            self.assertEqual(generated(cyclic_algebra(n), ((i, j),))[0],
                             normal_form(tuple(x % d for x in range(n))))


class Certificate(unittest.TestCase):

    def setUp(self) -> None:
        self.alg = cyclic_algebra(30)
        self.cert = certificate(self.alg)

    def test_replay_accepts(self) -> None:
        """The emitted certificate passes the engine-side replay."""
        self.assertTrue(verify_certificate(self.alg, self.cert).is_ok)

    def test_replay_accepts_small(self) -> None:
        """So do the certificates of the small algebras."""
        for alg in (cyclic_algebra(6), TWO_OPS):
            self.assertTrue(verify_certificate(alg, certificate(alg)).is_ok)

    def test_changed_meet_rejected(self) -> None:
        """A meet table with one entry changed fails the replay."""
        row = self.cert.meet[1]
        bad = replace(self.cert, meet=(self.cert.meet[0], (7,) + row[1:])
                      + self.cert.meet[2:])
        self.assertTrue(verify_certificate(self.alg, bad).is_err)

    def test_changed_trace_rejected(self) -> None:
        """A principal trace with one justification changed fails the replay."""
        trace = self.cert.prin_traces[0][1]
        broken = (trace[0], Merge(trace[1].lhs, trace[1].rhs, Seed(0))) + trace[2:]
        rows: List[Tuple[Tuple[Merge, ...], ...]] = list(self.cert.prin_traces)
        rows[0] = (rows[0][0], broken) + rows[0][2:]
        bad = replace(self.cert, prin_traces=tuple(rows))
        self.assertTrue(verify_certificate(self.alg, bad).is_err)

    def test_trace_shape(self) -> None:
        """A principal trace starts with its seed and then follows successors."""
        trace = self.cert.prin_traces[3][9]
        self.assertEqual(trace[0], Merge(3, 9, Seed(0)))
        self.assertEqual(trace[1], Merge(4, 10, Translate(0, 0)))


class Golden(unittest.TestCase):

    def test_round_trip(self) -> None:
        """Regenerating reproduces the committed benchmark module byte for byte."""
        committed = read_text(DEFAULT_OUT)
        self.assertTrue(committed.is_ok, f"missing {DEFAULT_OUT}")
        self.assertEqual(committed.unwrap(), generate().unwrap())


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
