#!/usr/bin/env python3
"""
File: scripts/python/test_corpus_stats.py

Description: Tests for ``corpus_stats.py``.

  Dependency-free: run directly with ``python3 scripts/python/test_corpus_stats.py``
  (prints ``N/N passed`` and exits non-zero on failure) or under ``pytest`` if it
  is installed.  Nothing here needs Agda, MkDocs, or the real tree: each test is
  a small literate fragment, a snippet of one of the three toolchain files, or a
  page written into a temporary directory.
"""
from __future__ import annotations

import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import corpus_stats as cs  # noqa: E402

# One scratch directory for the whole suite; cleaned up at interpreter exit.
_TMP = tempfile.TemporaryDirectory(prefix="corpus-stats-test-")


def module(*blocks: str, pragma: str = "--cubical-compatible --exact-split --safe") -> str:
    """A minimal literate module: a hidden preamble fence carrying the OPTIONS
    pragma, then one visible fence per extra block."""
    head = ("<!--\n"
            "```agda\n"
            f"{{-# OPTIONS {pragma} #-}}\n"
            "module M where\n"
            "```\n"
            "-->\n")
    body = "".join(f"\nsome prose\n\n```agda\n{b}\n```\n" for b in blocks)
    return head + body


# --------------------------------------------------------------------------- #
# module_stats: lines of Agda, and whether the module is checked under --safe.
# --------------------------------------------------------------------------- #
def test_counts_the_hidden_preamble_fence() -> None:
    # Agda checks the hidden preamble, so its two lines count.
    assert cs.module_stats(module())[0] == 2


def test_counts_visible_fences_and_not_prose_or_delimiters() -> None:
    loc, _ = cs.module_stats(module("f : Set\nf = ?", "g : Set"))
    assert loc == 2 + 2 + 1


def test_blank_lines_inside_a_fence_count() -> None:
    # "Lines of Agda" is the size of the code block, not its non-empty lines;
    # the committed figure has always been counted this way.
    assert cs.module_stats(module("f : Set\n\nf = ?"))[0] == 2 + 3


def test_safe_pragma_is_detected() -> None:
    assert cs.module_stats(module())[1] is True


def test_module_without_safe_is_not_counted_as_checked() -> None:
    assert cs.module_stats(module(pragma="--cubical-compatible"))[1] is False


def test_safe_is_matched_as_a_whole_option() -> None:
    # A longer option that merely starts with "--safe" must not satisfy it.
    assert cs.module_stats(module(pragma="--safety-net"))[1] is False


def test_options_pragma_quoted_in_prose_is_ignored() -> None:
    # The pragma is read from the fenced code, so prose showing an example
    # cannot make an unsafe module look safe.
    text = ("Modules in this library open with `{-# OPTIONS --safe #-}`.\n"
            + module(pragma="--cubical-compatible"))
    assert cs.module_stats(text)[1] is False


def test_a_commented_out_safe_pragma_does_not_count() -> None:
    # Agda applies the pragma on the next line, not the disabled one; a raw
    # search over the fence body would take the first and call this safe.
    text = ("<!--\n```agda\n-- {-# OPTIONS --safe #-}\n"
            "{-# OPTIONS --cubical-compatible #-}\nmodule M where\n```\n-->\n")
    assert cs.module_stats(text)[1] is False


def test_a_safe_pragma_inside_a_block_comment_does_not_count() -> None:
    text = ("<!--\n```agda\n{- a note:\n{-# OPTIONS --safe #-}\n-}\n"
            "module M where\n```\n-->\n")
    assert cs.module_stats(text)[1] is False


def test_a_pragma_after_the_module_header_does_not_count() -> None:
    # Agda requires OPTIONS before the header and rejects it after, so a tool
    # that honored one there would disagree with the type-checker.
    text = "<!--\n```agda\nmodule M where\n{-# OPTIONS --safe #-}\n```\n-->\n"
    assert cs.module_stats(text)[1] is False


def test_a_pragma_behind_another_pragma_still_counts() -> None:
    text = ("<!--\n```agda\n{-# BUILTIN NATURAL N #-}\n"
            "{-# OPTIONS --safe #-}\nmodule M where\n```\n-->\n")
    assert cs.module_stats(text)[1] is True


def test_a_pragma_split_across_lines_still_counts() -> None:
    text = ("<!--\n```agda\n{-# OPTIONS --cubical-compatible\n"
            "            --safe #-}\nmodule M where\n```\n-->\n")
    assert cs.module_stats(text)[1] is True


# --------------------------------------------------------------------------- #
# corpus: the aggregate over the tree.
# --------------------------------------------------------------------------- #
def test_corpus_aggregates_modules_loc_and_safe() -> None:
    texts = [module("f = ?"), module("g = ?", pragma="--cubical-compatible")]
    assert cs.corpus(texts) == cs.Corpus(modules=2, loc=6, safe=1)


def test_measure_rejects_a_missing_src_rather_than_counting_zero() -> None:
    # Publishing "0 literate modules", or writing it into the page, is worse
    # than failing: it means the tool is looking at the wrong place.
    got = cs.measure(Path(_TMP.name) / "no-such-tree")
    assert got.is_err
    assert "not a directory" in got.unwrap_err().message


def test_measure_rejects_an_empty_src() -> None:
    empty = Path(_TMP.name) / "empty-src"
    empty.mkdir(exist_ok=True)
    got = cs.measure(empty)
    assert got.is_err
    assert "no literate modules" in got.unwrap_err().message


# --------------------------------------------------------------------------- #
# Stats.markers: how the numbers are rendered on the page.
# --------------------------------------------------------------------------- #
def markers(modules: int, loc: int, safe: int) -> dict[str, str]:
    return cs.Stats(corpus=cs.Corpus(modules=modules, loc=loc, safe=safe),
                    toolchain=cs.Toolchain(agda="2.8.0", stdlib="2.3")).markers


def test_loc_rounds_half_up_not_to_even() -> None:
    # round() would give "60k" for 60_500 (ties to even); a reader of a "…k"
    # stat expects 61k.
    assert markers(1, 60_500, 1)["loc"] == "61k"
    assert markers(1, 60_499, 1)["loc"] == "60k"
    assert markers(1, 67_175, 1)["loc"] == "67k"


def test_checked_share_floors_and_never_rounds_up_to_a_false_hundred() -> None:
    assert markers(339, 1, 339)["checked"] == "100%"
    assert markers(339, 1, 338)["checked"] == "99%"
    assert markers(3, 1, 2)["checked"] == "66%"


def test_checked_share_on_an_empty_tree_does_not_divide_by_zero() -> None:
    assert markers(0, 0, 0)["checked"] == "0%"


def test_toolchain_values_pass_through() -> None:
    assert markers(1, 1, 1)["agda"] == "2.8.0"
    assert markers(1, 1, 1)["stdlib"] == "2.3"


# --------------------------------------------------------------------------- #
# fill / marker_names / unfilled: the marker substitution itself.
# --------------------------------------------------------------------------- #
STRIP = ('<span><!-- ualib:stat:modules -->302<!-- /ualib:stat:modules --></span>\n'
         '<span>Agda <!-- ualib:stat:agda -->2.8.0<!-- /ualib:stat:agda --> · '
         'stdlib <!-- ualib:stat:stdlib -->2.3<!-- /ualib:stat:stdlib --></span>\n')


def test_fill_replaces_the_value_and_keeps_the_markers() -> None:
    out = cs.fill(STRIP, {"modules": "339"})
    assert "<!-- ualib:stat:modules -->339<!-- /ualib:stat:modules -->" in out
    assert "302" not in out


def test_fill_handles_two_markers_on_one_line() -> None:
    out = cs.fill(STRIP, {"agda": "2.9.0", "stdlib": "2.4"})
    assert "Agda <!-- ualib:stat:agda -->2.9.0<!-- /ualib:stat:agda --> · " in out
    assert "stdlib <!-- ualib:stat:stdlib -->2.4<!-- /ualib:stat:stdlib -->" in out


def test_fill_leaves_a_marker_it_does_not_compute_alone() -> None:
    assert cs.fill(STRIP, {}) == STRIP


def test_fill_spans_a_marker_split_across_lines() -> None:
    split = "<!-- ualib:stat:loc -->\n60k\n<!-- /ualib:stat:loc -->"
    assert cs.fill(split, {"loc": "67k"}) == \
        "<!-- ualib:stat:loc -->67k<!-- /ualib:stat:loc -->"


def test_fill_is_idempotent() -> None:
    values = {"modules": "339", "agda": "2.8.0", "stdlib": "2.3"}
    once = cs.fill(STRIP, values)
    assert cs.fill(once, values) == once


def test_marker_names_reads_the_page() -> None:
    assert cs.marker_names(STRIP) == {"modules", "agda", "stdlib"}


def test_unfilled_names_the_stats_the_page_is_missing() -> None:
    assert cs.unfilled(STRIP, {"modules": "339", "loc": "67k", "checked": "100%"}) \
        == ("checked", "loc")


# --------------------------------------------------------------------------- #
# toolchain: the declared versions, reconciled against the pins that bind.
# --------------------------------------------------------------------------- #
MKDOCS = 'extra:\n  agda_version: "2.8.0"\n  stdlib_version: "2.3"\n'
LIB = "name: agda-algebras\ndepend: standard-library-2.3\ninclude: src\n"
FLAKE = ('case "${agdaVer}" in\n  2.8.*) : ;;\n  *) echo warn ;;\nesac\n'
         'case "${stdlibVer}" in\n  2.3*) : ;;\n  *) echo warn ;;\nesac\n')


def test_toolchain_reads_all_three_files() -> None:
    got = cs.toolchain(MKDOCS, LIB, FLAKE)
    assert got.is_ok
    assert got.unwrap() == cs.Toolchain(agda="2.8.0", stdlib="2.3")


def test_toolchain_rejects_a_site_variable_that_disagrees_with_the_agda_lib() -> None:
    # The dependency Agda enforces is the pin that binds; the site variable
    # quoting a different stdlib is the drift this check exists to catch.
    got = cs.toolchain(MKDOCS.replace('"2.3"', '"2.4"'), LIB, FLAKE)
    assert got.is_err
    assert "standard-library-2.3" in got.unwrap_err().message


def test_toolchain_rejects_an_agda_version_outside_the_flake_guard() -> None:
    got = cs.toolchain(MKDOCS.replace('"2.8.0"', '"2.9.0"'), LIB, FLAKE)
    assert got.is_err
    assert "2.8 series" in got.unwrap_err().message


def test_toolchain_rejects_an_agda_lib_outside_the_flake_guard() -> None:
    got = cs.toolchain(MKDOCS.replace('"2.3"', '"2.4"'),
                       LIB.replace("2.3", "2.4"), FLAKE)
    assert got.is_err
    assert "2.3 series" in got.unwrap_err().message


def test_toolchain_reports_the_file_whose_shape_changed() -> None:
    # A source of truth that cannot be read must fail loudly, not drop out of
    # the check.
    got = cs.toolchain(MKDOCS, "name: agda-algebras\ninclude: src\n", FLAKE)
    assert got.is_err
    assert "agda-algebras.agda-lib" in got.unwrap_err().message


def test_flake_guard_series_are_parsed_from_both_shapes() -> None:
    # The Agda guard is written `2.8.*)` and the stdlib guard `2.3*)`.
    assert cs._guard("agdaVer").search(FLAKE).group(1) == "2.8"
    assert cs._guard("stdlibVer").search(FLAKE).group(1) == "2.3"


def test_in_series_does_not_accept_a_bare_string_prefix() -> None:
    assert cs._in_series("2.8.0", "2.8")
    assert cs._in_series("2.8", "2.8")
    # 2.80 starts with "2.8" as text but is a different series.
    assert not cs._in_series("2.80", "2.8")


# --------------------------------------------------------------------------- #
# analyze: what the gate reports about a page on disk.
# --------------------------------------------------------------------------- #
def page(text: str, name: str) -> Path:
    """Write ``text`` to a page in the suite's temporary directory."""
    path = Path(_TMP.name) / name
    path.write_text(text, encoding="utf-8")
    return path


VALUES = {"modules": "339", "agda": "2.8.0", "stdlib": "2.3"}


def test_analyze_reports_no_drift_when_the_page_is_current() -> None:
    got = cs.analyze(VALUES, [page(cs.fill(STRIP, VALUES), "current.md")])
    assert got.is_ok
    assert got.unwrap() == ()


def test_analyze_reports_the_page_and_a_diff_when_a_value_drifted() -> None:
    got = cs.analyze(VALUES, [page(STRIP, "drifted.md")])
    assert got.is_ok
    drift, = got.unwrap()
    assert drift.stale
    assert drift.path.name == "drifted.md"
    assert "302" in drift.diff and "339" in drift.diff


def test_analyze_fails_when_the_page_lost_a_marker() -> None:
    # A renamed or misspelled marker would otherwise leave a hand-typed number
    # standing while the gate reported success.
    got = cs.analyze({**VALUES, "loc": "67k"}, [page(STRIP, "no-loc.md")])
    assert got.is_err
    assert "no marker for loc" in got.unwrap_err().message


def test_analyze_fails_when_a_page_is_missing() -> None:
    got = cs.analyze(VALUES, [Path("does/not/exist.md")])
    assert got.is_err


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
