#!/usr/bin/env python3
"""Tests for ``unused_imports.py``.

Dependency-free: run directly with ``python3 scripts/python/test_unused_imports.py``
(prints ``OK`` and exits 0 on success) or under ``pytest`` if it is installed.
Each scenario is a small literate ``.lagda.md`` fragment exercising one feature
of the analyzer.
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import unused_imports as ui  # noqa: E402


def flagged(text: str) -> dict[str, tuple[str, ...]]:
    """Run the analyzer on a fragment and return ``{module: unused names}``."""
    report = ui.analyze_file(Path("T.lagda.md"), text)
    return {f.module: f.unused for f in report.findings}


def block(*code: str) -> str:
    """Wrap Agda lines in a ```` ```agda ```` fenced block."""
    return "```agda\n" + "\n".join(code) + "\n```\n"


# --------------------------------------------------------------------------- #
# Closed `using` lists: per-name and whole-statement detection
# --------------------------------------------------------------------------- #

def test_partial_unused_name() -> None:
    text = block(
        "open import M using ( a ; b ; c )",
        "foo = a",
    )
    assert flagged(text) == {"M": ("b", "c")}


def test_all_unused_is_statement() -> None:
    text = block(
        "open import M using ( a ; b )",
        "foo = bar",
    )
    report = ui.analyze_file(Path("T.lagda.md"), text)
    assert [f.category for f in report.findings] == ["statement"]
    assert report.findings[0].unused == ("a", "b")


def test_all_used_is_clean() -> None:
    text = block(
        "open import M using ( a ; b )",
        "foo = a b",
    )
    assert flagged(text) == {}


# --------------------------------------------------------------------------- #
# Use sites that are easy to miss
# --------------------------------------------------------------------------- #

def test_used_in_module_telescope() -> None:
    # `Signature`, `𝓞`, `𝓥` are used only in the module header — still "used".
    text = block(
        "open import Overture using ( 𝓞 ; 𝓥 ; Signature )",
        "module T.Foo {𝑆 : Signature 𝓞 𝓥} where",
        "bar = 𝑆",
    )
    assert flagged(text) == {}


def test_used_only_in_later_import_args() -> None:
    # `𝑆` is referenced only inside a later module application's arguments.
    text = block(
        "open import Overture using ( Signature )",
        "module T.Foo {𝑆 : Signature} where",
        "open import Other using ( g ) renaming ( h to k )",
    )
    # `Signature` is used (header); g and k from Other are unused.
    assert flagged(text) == {"Other": ("g", "k")}


# --------------------------------------------------------------------------- #
# Mixfix / operator names
# --------------------------------------------------------------------------- #

def test_mixfix_used_infix() -> None:
    text = block(
        "open import Alg using ( _∙_ )",
        "foo a b = a ∙ b",
    )
    assert flagged(text) == {}


def test_mixfix_unused() -> None:
    text = block(
        "open import Alg using ( _∙_ ; _∘_ )",
        "foo a b = a ∙ b",
    )
    assert flagged(text) == {"Alg": ("_∘_",)}


def test_mixfix_outer_bars() -> None:
    text = block(
        "open import Q using ( ∣_∣ )",
        "card x = ∣ x ∣",
    )
    assert flagged(text) == {}


def test_syntax_backed_name_used_via_notation() -> None:
    # `Σ-syntax` is used as `Σ[ x ∈ A ] B`, never as the token `Σ-syntax`.
    text = block(
        "open import Data.Product using ( Σ-syntax )",
        "foo = Σ[ x ∈ A ] B x",
    )
    assert flagged(text) == {}


def test_syntax_backed_name_genuinely_unused() -> None:
    text = block(
        "open import Data.Product using ( Σ-syntax )",
        "foo = bar",
    )
    assert flagged(text) == {"Data.Product": ("Σ-syntax",)}


# --------------------------------------------------------------------------- #
# renaming, empty using, aliases
# --------------------------------------------------------------------------- #

def test_renaming_target_used() -> None:
    text = block(
        "open import Agda.Primitive using () renaming ( Set to Type )",
        "foo : Type",
    )
    assert flagged(text) == {}


def test_renaming_target_unused() -> None:
    text = block(
        "open import Agda.Primitive using () renaming ( Set to Type )",
        "foo = bar",
    )
    assert flagged(text) == {"Agda.Primitive": ("Type",)}


def test_using_and_renaming_mixed() -> None:
    text = block(
        "open import F using ( _∘_ ) renaming ( Func to _⟶_ )",
        "foo = _∘_",
    )
    # `_⟶_` is unused; `_∘_` is used by its full form.
    assert flagged(text) == {"F": ("_⟶_",)}


def test_alias_used_qualified() -> None:
    text = block(
        "open import Relation.Binary.PropositionalEquality as ≡ using ( _≡_ )",
        "foo = ≡.refl",
        "bar : _≡_",
    )
    assert flagged(text) == {}


def test_alias_unused() -> None:
    text = block(
        "open import Relation.Binary.PropositionalEquality as ≡ using ( _≡_ )",
        "bar : _≡_",
    )
    assert flagged(text) == {"Relation.Binary.PropositionalEquality": ("≡",)}


# --------------------------------------------------------------------------- #
# public, whole-module opens, qualified imports
# --------------------------------------------------------------------------- #

def test_public_never_flagged() -> None:
    text = block(
        "open import M using ( a ; b ) public",
        "foo = bar",
    )
    assert flagged(text) == {}


def test_whole_module_open_not_flagged() -> None:
    text = block(
        "open import M",
        "foo = bar",
    )
    report = ui.analyze_file(Path("T.lagda.md"), text)
    assert report.findings == ()
    assert len(report.open_ended) == 1


def test_qualified_import_unused() -> None:
    text = block(
        "import Algebra.Definitions",
        "foo = bar",
    )
    assert flagged(text) == {"Algebra.Definitions": ("Algebra.Definitions",)}


def test_qualified_import_reused() -> None:
    text = block(
        "import Algebra.Definitions",
        "open Algebra.Definitions (_≈_)",
    )
    assert flagged(text) == {}


def test_qualified_import_as_used() -> None:
    text = block(
        "import Relation.Binary.Reasoning.PartialOrder as ≤-Reasoning",
        "foo = ≤-Reasoning.begin",
    )
    assert flagged(text) == {}


# --------------------------------------------------------------------------- #
# Multi-line, repeated clauses, multiple opens per line
# --------------------------------------------------------------------------- #

def test_multiline_using_list() -> None:
    text = block(
        "open  import M {𝑆 = 𝑆}",
        "      using ( a ; b ;",
        "              c ; d )",
        "foo = a c",
    )
    assert flagged(text) == {"M": ("b", "d")}


def test_repeated_using_clauses() -> None:
    text = block(
        "open  import M {𝑆 = 𝑆}",
        "      using ( a ; b )",
        "      using ( c ; d )",
        "foo = a d",
    )
    assert flagged(text) == {"M": ("b", "c")}


def test_multiple_opens_one_line() -> None:
    text = block(
        "open H using ( h ) ; open S using ( s )",
        "foo = h",
    )
    assert flagged(text) == {"S": ("s",)}


# --------------------------------------------------------------------------- #
# Comments and strings must not confuse the parser
# --------------------------------------------------------------------------- #

def test_trailing_comment_with_paren() -> None:
    # The trailing comment contains `)` and `;` that must not break parsing.
    text = block(
        "open import M using ( Term ) -- ; _⟦_⟧ )",
        "foo = bar",
    )
    assert flagged(text) == {"M": ("Term",)}


def test_use_only_in_comment_is_unused() -> None:
    text = block(
        "open import M using ( a )",
        "foo = bar  -- mentions a in a comment only",
    )
    assert flagged(text) == {"M": ("a",)}


def test_block_commented_import_ignored() -> None:
    text = block(
        "{- open import Fake using ( ghost ) -}",
        "open import M using ( a )",
        "foo = a",
    )
    assert flagged(text) == {}


def test_module_keyword_item() -> None:
    text = block(
        "open import S using ( module Environment ; comm-hom-term )",
        "foo = Environment.bar",
    )
    assert flagged(text) == {"S": ("comm-hom-term",)}


def test_module_item_used_by_reopen() -> None:
    # `module Environment` is used only by being re-opened, not by a token.
    text = block(
        "open import S using ( module Environment ; comm-hom-term )",
        "open Environment 𝑨 using () renaming ( ⟦_⟧ to ⟦_⟧₁ )",
        "foo = comm-hom-term ⟦_⟧₁",
    )
    assert flagged(text) == {}


def test_module_item_genuinely_unused() -> None:
    text = block(
        "open import S using ( module Environment ; comm-hom-term )",
        "foo = comm-hom-term",
    )
    assert flagged(text) == {"S": ("Environment",)}


# --------------------------------------------------------------------------- #
# Literate extraction: hidden (HTML-commented) blocks count as code
# --------------------------------------------------------------------------- #

def test_hidden_block_counts_as_code() -> None:
    text = (
        block("open import M using ( a )")
        + "\nsome prose\n\n<!--\n"
        + block("foo = a")
        + "-->\n"
    )
    assert flagged(text) == {}


def test_prose_is_ignored() -> None:
    # An import-looking line in prose (outside a code block) is not parsed.
    text = "Consider `open import M using ( a )` in prose.\n" + block(
        "open import N using ( b )", "foo = b"
    )
    assert flagged(text) == {}


# --------------------------------------------------------------------------- #
# Runner
# --------------------------------------------------------------------------- #

def _run() -> int:
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    failures = []
    for t in tests:
        try:
            t()
        except AssertionError as e:  # noqa: PERF203
            failures.append((t.__name__, e))
    for name, err in failures:
        print(f"FAIL {name}: {err}")
    print(f"{len(tests) - len(failures)}/{len(tests)} passed")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(_run())
