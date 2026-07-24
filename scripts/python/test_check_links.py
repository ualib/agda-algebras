#!/usr/bin/env python3
"""Tests for ``check_links.py``.

Dependency-free: run directly with ``python3 scripts/python/test_check_links.py``
(prints ``OK`` and exits 0 on success) or under ``pytest`` if it is installed.
Each scenario is a small Markdown fragment exercising one rule of the reference
scanner.
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import check_links as cl  # noqa: E402


def refs(text: str) -> list[str]:
    """The reference ids the scanner sees as links (order preserved)."""
    return [ref for _, ref, _ in cl.iter_uses(text)]


def undefined(text: str, defs: set[str]) -> list[str]:
    """Reference ids used in ``text`` that do not resolve against ``defs`` or the
    page's own definitions (using the checker's real resolution rule)."""
    known = defs | cl.defined_labels(text)
    return [ref for _, ref, _ in cl.iter_uses(text) if not cl.is_resolved(ref, known)]


# --------------------------------------------------------------------------- #
# norm: markdown reference ids are case-insensitive, whitespace-collapsed.
# --------------------------------------------------------------------------- #
def test_norm() -> None:
    assert cl.norm("ADR-008") == "adr-008"
    assert cl.norm("  Setoid.Congruences.Finite.Basic ") == "setoid.congruences.finite.basic"
    assert cl.norm("Agda   Universal\tAlgebra") == "agda universal algebra"


# --------------------------------------------------------------------------- #
# The two reference shapes the corpus uses.
# --------------------------------------------------------------------------- #
def test_collapsed_reference() -> None:
    assert refs("see [ADR-008][] for the rationale") == ["adr-008"]


def test_full_reference_uses_the_ref_not_the_text() -> None:
    # Display text is a code span; the *ref* is the bare module label.
    assert refs("[`Setoid.Varieties.HSP`][Setoid.Varieties.HSP] here") \
        == ["setoid.varieties.hsp"]


def test_inline_link_is_not_a_reference() -> None:
    # [text](url) has no `][`, so it is never a reference usage.
    assert refs("an [inline](https://example.com) link") == []


def test_shortcut_reference_is_not_checked() -> None:
    # Bare [text] is ambiguous against ordinary bracket prose; out of scope.
    assert refs("a bare [label] and a footnote [^1] marker") == []


# --------------------------------------------------------------------------- #
# Things that render verbatim must be skipped.
# --------------------------------------------------------------------------- #
def test_skips_fenced_code() -> None:
    text = "before [A][]\n```agda\nxs [ i ][ j ]  -- not a link\n```\nafter [B][]"
    assert refs(text) == ["a", "b"]


def test_skips_inline_code_span() -> None:
    # The site-guide documents the syntax with a literal `[Some Name][]` sample.
    assert refs("To make `[Some Name][]` resolve, add a definition.") == []


def test_skips_multi_backtick_code_span() -> None:
    # A run of N backticks closes on the next run of N, so a double-backtick span
    # (the kramdown ``` ``x`{.AgdaRecord}`` ``` idiom) is skipped whole, and its
    # inner single backticks do not leak reference-like text out of the span.
    assert refs("prose ``literal [Foo][] text`` after") == []
    assert refs("span ``a `Algebra`{.x} b`` then [ADR-008][]") == ["adr-008"]


def test_evaluates_backticked_text_in_a_collapsed_ref() -> None:
    # Backticks INSIDE the link text (not wrapping the whole thing) do not make
    # it a code span: [`X`][] is still a (broken, if undefined) collapsed ref.
    assert refs("[`Classical.Structures.Reduct`][] was built by hand") \
        == ["`classical.structures.reduct`"]


def test_skips_single_line_html_comment() -> None:
    assert refs("prose <!-- hidden [A][] --> tail [B][]") == ["b"]


def test_skips_multiline_html_comment() -> None:
    text = "keep [A][]\n<!--\n```agda\nimport [Ignored][]\n```\n-->\nkeep [B][]"
    assert refs(text) == ["a", "b"]


# --------------------------------------------------------------------------- #
# Definition collection + the end-to-end undefined check.
# --------------------------------------------------------------------------- #
def test_defined_labels_collects_defs_but_not_footnotes() -> None:
    text = "[Overture]: /Overture/\n[^1]: a footnote definition\n"
    assert cl.defined_labels(text) == {"overture"}


def test_page_local_definition_satisfies_a_reference() -> None:
    text = "see [`DEPRECATED.md`][DEPRECATED] for detail\n\n[DEPRECATED]: https://x/y\n"
    assert undefined(text, set()) == []


def test_undefined_reference_is_reported() -> None:
    assert undefined("see [ADR-008][] here", {"adr-007"}) == ["adr-008"]


def test_global_definition_satisfies_a_reference() -> None:
    assert undefined("see [ADR-008][] here", {"adr-008"}) == []


def test_backticked_reference_label_never_resolves() -> None:
    # python-markdown consumes the backticks as a code span before resolving the
    # reference, so `[text][`path`]` renders broken even with a matching "def".
    # (The STYLE_GUIDE regression that slipped past an earlier version.)
    text = "see [Milestone 2][`docs/GITHUB_PROJECT.md`]\n\n[`docs/GITHUB_PROJECT.md`]: /x/\n"
    assert undefined(text, set()) == ["`docs/github_project.md`"]
    # The clean fix — a plain-label ref — resolves.
    assert undefined("see [Milestone 2][ROADMAP]", {"roadmap"}) == []


# --------------------------------------------------------------------------- #
def main() -> int:
    tests = [v for k, v in sorted(globals().items())
             if k.startswith("test_") and callable(v)]
    for t in tests:
        t()
    print(f"OK ({len(tests)} tests)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
