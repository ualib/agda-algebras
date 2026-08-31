"""Tests for the A5 simplicity-certificate generator (`make flrp-test`).

Three things are checked:

+ the group construction — the 60 even permutations in lexicographic order
  form a group under the emitted tables, with the identity at index 0 and
  the stated generators at their indices;
+ the certificate, replayed engine-side — for every non-identity element
  the seed words reach both generators through conjugates, and the shared
  word table expresses all 60 elements in the generators; this mirrors the
  Agda checker's obligations as a tripwire only, the Agda module remaining
  the sole authority;
+ the golden round trip — regenerating must reproduce the committed
  ``Tables`` module byte for byte (the generator is a deterministic
  function of nothing).
"""

from __future__ import annotations

import unittest

from a5_simple_cert import (DEFAULT_OUT, ORDER, One, build_tables, compose,
                            eval_term, generate, generator_words, invert,
                            is_even, seed_words)


class GroupConstruction(unittest.TestCase):

    def setUp(self) -> None:
        self.g = build_tables()

    def test_order_and_identity(self) -> None:
        """A5 has 60 elements; index 0 is the identity of the table."""
        self.assertEqual(len(self.g.mul), ORDER)
        self.assertEqual(self.g.act[0], (0, 1, 2, 3, 4))
        self.assertTrue(all(self.g.mul[0][a] == a == self.g.mul[a][0]
                            for a in range(ORDER)))

    def test_generators(self) -> None:
        """The generators are the 5-cycle (0 1 2 3 4) and the 3-cycle (0 1 2)."""
        self.assertEqual(self.g.act[self.g.gen_s], (1, 2, 3, 4, 0))
        self.assertEqual(self.g.act[self.g.gen_t], (1, 2, 0, 3, 4))

    def test_group_laws(self) -> None:
        """Inverses invert, parity is even, and the action is a faithful hom."""
        for a in range(ORDER):
            self.assertTrue(is_even(self.g.act[a]))
            self.assertEqual(self.g.act[self.g.inv[a]], invert(self.g.act[a]))
            for b in range(ORDER):
                self.assertEqual(self.g.act[self.g.mul[a][b]],
                                 compose(self.g.act[a], self.g.act[b]))
        self.assertEqual(len({self.g.act[a] for a in range(ORDER)}), ORDER)


class Certificate(unittest.TestCase):

    def setUp(self) -> None:
        self.g = build_tables()

    def test_generator_words_cover(self) -> None:
        """The shared word table expresses every element in the generators."""
        words = generator_words(self.g)
        self.assertEqual(len(words), ORDER)
        sigma = [self.g.gen_s, self.g.gen_t]
        self.assertTrue(all(eval_term(w, sigma, self.g) == y
                            for y, w in enumerate(words)))
        self.assertIsInstance(words[0], One)

    def test_seed_words_certify_simplicity(self) -> None:
        """Every non-identity element normally generates both generators."""
        for x in range(1, ORDER):
            term_s, term_t = seed_words(x, self.g)
            self.assertEqual(eval_term(term_s, [x], self.g), self.g.gen_s)
            self.assertEqual(eval_term(term_t, [x], self.g), self.g.gen_t)


class Golden(unittest.TestCase):

    def test_round_trip(self) -> None:
        """Regenerating reproduces the committed Tables module byte for byte."""
        self.assertTrue(DEFAULT_OUT.exists(), f"missing {DEFAULT_OUT}")
        self.assertEqual(DEFAULT_OUT.read_text(), generate())


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
