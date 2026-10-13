#!/usr/bin/env python3
"""
File: scripts/python/test_barrels.py

Description: Tests for ``barrels.py`` and the front-matter reader it added to
  ``_utils/literate.py``.

  Dependency-free: run directly with ``python3 scripts/python/test_barrels.py``
  (prints ``N/N passed`` and exits 0 on success) or under ``pytest`` if it is
  installed.  Each scenario is a small tree of literate ``.lagda.md`` modules
  held in memory; only the exit-status test writes files, to a temporary
  directory.  Nothing here needs Agda.
"""
from __future__ import annotations

import io
import json
import os
import sys
import tempfile
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import barrels as b  # noqa: E402
from _utils.literate import front_matter, front_matter_end, strip_front_matter  # noqa: E402

ROOT = Path("src")


def front(name: str, extra: str = "") -> str:
    """A module's front matter, as the corpus writes it."""
    path = name.replace(".", "/")
    return (f'---\nlayout: default\nfile: "src/{path}.lagda.md"\n'
            f'title : "{name} module"\ndate : "2026-10-13"\n{extra}'
            'author: "the agda-algebras development team"\n---\n\n')


def module(name: str, *code: str, extra: str = "", hidden_pragma: bool = True) -> str:
    """A literate module: front matter, prose, the pragma in a fence hidden in
    an HTML comment (as the root module has it), then the code."""
    pragma = "{-# OPTIONS --without-K --exact-split --safe #-}"
    preamble = (f"<!--\n```agda\n{pragma}\n```\n-->\n\n" if hidden_pragma
                else f"```agda\n{pragma}\n```\n\n")
    return (front(name, extra) + f"This is the {name} module.\n\n" + preamble
            + "```agda\n" + "\n".join(code) + "\n```\n")


def barrel(name: str, *imports: str, public: bool = True) -> str:
    suffix = " public" if public else ""
    return module(name, f"module {name} where", "",
                  *(f"open import {i}{suffix}" for i in imports))


def leaf(name: str, *imports: str, heavy: bool = False) -> str:
    extra = "check-cost: heavy\n" if heavy else ""
    return module(name, *(f"open import {i} using ( x )" for i in imports),
                  "", f"module {name} where", "", "x : Set₁", "x = Set", extra=extra)


def tree_of(files: dict[str, str]) -> b.Tree:
    return b.scan_tree(ROOT, [(ROOT / (n.replace(".", "/") + ".lagda.md"), t)
                              for n, t in files.items()])


def report_of(files: dict[str, str], built: frozenset[str] | None = None,
              legacy: bool = False) -> b.Report:
    tree = tree_of(files)
    everything = frozenset(tree.modules) if built is None else built
    return b.check(tree, everything, (ROOT / "Everything.agda",), legacy)


def shape(name: str, text: str) -> b.Shape:
    return tree_of({name: text}).modules[name].shape


def kinds(report: b.Report) -> list[str]:
    return [p.kind.value for p in report.problems]


# The motivating case: a barrel chain down to a generated heavy module.
A5 = {
    "agda-algebras": barrel("agda-algebras", "Examples", public=False),
    "Examples": barrel("Examples", "Examples.Classical", public=False),
    "Examples.Classical": barrel("Examples.Classical", "Examples.Classical.Groups"),
    "Examples.Classical.Groups": barrel("Examples.Classical.Groups",
                                        "Examples.Classical.Groups.Cyclic",
                                        "Examples.Classical.Groups.A5", public=False),
    "Examples.Classical.Groups.Cyclic": leaf("Examples.Classical.Groups.Cyclic"),
    "Examples.Classical.Groups.A5": leaf("Examples.Classical.Groups.A5",
                                         "Examples.Classical.Groups.A5.Tables"),
    "Examples.Classical.Groups.A5.Tables": leaf("Examples.Classical.Groups.A5.Tables",
                                                "Data.Vec.Base", heavy=True),
}


# --------------------------------------------------------------------------- #
# The front-matter reader
# --------------------------------------------------------------------------- #

def test_front_matter_reads_space_before_colon() -> None:
    entries = front_matter(front("A.B", "check-cost: heavy\n"))
    assert entries["title"] == "A.B module", entries
    assert entries["date"] == "2026-10-13"
    assert entries["check-cost"] == "heavy"


def test_front_matter_unquotes_and_skips_non_entries() -> None:
    text = "---\nkey: 'single'\n  indented continuation\n# a comment\nk2:\n---\nbody: no\n"
    assert dict(front_matter(text)) == {"key": "single", "k2": ""}


def test_front_matter_absent_or_unclosed() -> None:
    assert dict(front_matter("n---\nlayout: default\n---\n")) == {}
    assert dict(front_matter("---\nlayout: default\n")) == {}
    assert front_matter_end("n---\na: b\n---".split("\n")) == 0


def test_strip_front_matter_uses_the_same_block() -> None:
    lines = tuple(front("A", "check-cost: heavy\n").split("\n")) + ("prose",)
    assert strip_front_matter(lines) == lines[front_matter_end(lines):]
    assert strip_front_matter(lines)[-1] == "prose"
    assert strip_front_matter(("---", "a: b")) == ("---", "a: b")


# --------------------------------------------------------------------------- #
# Shapes: what counts as a barrel
# --------------------------------------------------------------------------- #

def test_public_barrel_is_a_barrel() -> None:
    assert shape("A", barrel("A", "A.B", "A.C")) is b.Shape.BARREL


def test_plain_open_import_barrel_is_a_barrel() -> None:
    # Eight barrels, the root among them, re-export nothing; they cost the same.
    assert shape("A", barrel("A", "A.B", public=False)) is b.Shape.BARREL


def test_visible_pragma_fence_is_the_same() -> None:
    text = module("A", "module A where", "open import A.B public", hidden_pragma=False)
    assert shape("A", text) is b.Shape.BARREL


def test_parameterized_header_with_imports_before_it() -> None:
    text = module("Overture.Terms",
                  "open import Overture using ( 𝓞 ; 𝓥 ; Signature )",
                  "module Overture.Terms {𝑆 : Signature 𝓞 𝓥} where",
                  "open import Overture.Terms.Basic {𝑆 = 𝑆} public")
    assert shape("Overture.Terms", text) is b.Shape.BARREL


def test_multiline_header_and_instance_binding() -> None:
    text = module("A", "module A", "  {X : Set}", "  ⦃ _ : X ⦄", "  where",
                  "open import A.B public")
    assert shape("A", text) is b.Shape.BARREL


def test_nested_parameter_module_is_still_a_barrel() -> None:
    # Legacy.Base.Varieties: one import needs a level, so it sits in `module _`.
    text = module("V", "module V where", "open import V.E public",
                  "open import Level using ( Level )",
                  "module _ {α : Level} where", "", " open import V.F {α = α} public")
    assert shape("V", text) is b.Shape.BARREL


def test_header_only_module() -> None:
    assert shape("P", module("P", "module P where")) is b.Shape.HEADER_ONLY


def test_definition_makes_a_module() -> None:
    assert shape("A", leaf("A", "A.B")) is b.Shape.MODULE


def test_import_then_open_is_a_barrel() -> None:
    # `import M` and `open M public` re-export what `open import M public` does.
    text = module("A", "module A where", "import A.B as B", "open B public")
    assert shape("A", text) is b.Shape.BARREL


def test_code_sharing_a_statement_line_makes_a_module() -> None:
    text = module("A", "module A where", "open import A.B public ; x = A.B.y")
    assert shape("A", text) is b.Shape.MODULE


def test_telescope_with_a_definition_makes_a_module() -> None:
    text = module("A", "module A (n : ℕ) where", "open import A.B public",
                  "module M = A.B")
    assert shape("A", text) is b.Shape.MODULE


def test_commented_out_import_is_not_an_import() -> None:
    text = module("A", "module A where", "-- open import A.Heavy public",
                  "{- open import A.Heavy public -}", "open import A.B public")
    tree = tree_of({"A": text, "A.B": leaf("A.B"), "A.Heavy": leaf("A.Heavy", heavy=True)})
    assert tree.graph["A"] == ("A.B",), tree.graph["A"]


# --------------------------------------------------------------------------- #
# Reading code as Agda reads it (each of these once hid a barrel or an edge)
# --------------------------------------------------------------------------- #

HEAVY = {"H": leaf("H", heavy=True)}


def raw(name: str, body: str, extra: str = "") -> str:
    """A module whose body after the front matter is given verbatim."""
    return front(name, extra) + "A module.\n\n" + body


def gate(files: dict[str, str]) -> list[str]:
    """The chains the gate reports, as `A → B` strings."""
    return [" → ".join(p.chain) for p in report_of(files).problems if p.chain]


def test_wrapped_module_arguments_continue_the_import() -> None:
    # Agda's layout rule: a line indented past the statement continues it.
    text = module("A", "module A {X : Set₁} where", "", "open import H",
                  "  {X = X} public")
    assert gate({**HEAVY, "A": text}) == ["A → H"]
    report = report_of({**HEAVY, "A": text})
    assert report.tree.modules["A"].shape is b.Shape.BARREL


def test_continuation_after_a_blank_line() -> None:
    text = module("A", "module A where", "open import H", "", "  public")
    assert gate({**HEAVY, "A": text}) == ["A → H"]


def test_a_bare_fence_is_agda_code() -> None:
    # The Makefile does not pass --literate-markdown-only-agda-blocks.
    body = "```agda\nmodule A where\n```\n\n```\nopen import H public\n```\n"
    assert gate({**HEAVY, "A": raw("A", body)}) == ["A → H"]


def test_indented_and_prefixed_fences_are_agda_code() -> None:
    indented = "```agda\nmodule A where\n```\n\n   ```agda\nopen import H public\n   ```\n"
    prefixed = "```agda\nmodule B where\n```\n\n<!-- ```agda\nopen import H public\n```\n-->\n"
    assert gate({**HEAVY, "A": raw("A", indented)}) == ["A → H"]
    assert gate({**HEAVY, "B": raw("B", prefixed)}) == ["B → H"]


def test_an_agda_fence_shown_inside_a_text_block_is_prose() -> None:
    body = ("```agda\nmodule A where\nopen import H public\n```\n\n"
            "A module is written like this:\n\n```text\n```agda\nx : Set₁\nx = Set\n```\n")
    report = report_of({**HEAVY, "A": raw("A", body)})
    assert report.tree.modules["A"].shape is b.Shape.BARREL
    assert gate({**HEAVY, "A": raw("A", body)}) == ["A → H"]


def test_an_attribute_fence_is_prose_to_agda() -> None:
    # Agda reads ```{.agda .hidden} as prose, and the ``` closing it as an opener.
    body = ("```agda\nmodule A where\nopen import H public\n```\n\n"
            "```{.agda .hidden}\nx : Set₁\n```\n\n```\n")
    assert report_of({**HEAVY, "A": raw("A", body)}).tree.modules["A"].shape is b.Shape.BARREL


def test_dashes_at_a_token_start_open_a_comment() -> None:
    text = module("A", "module A where", "open import H public",
                  "--| re-exports the heavy tables", "  --> and nothing else")
    assert gate({**HEAVY, "A": text}) == ["A → H"]


def test_dashes_inside_a_name_are_the_name() -> None:
    mid = module("M", "open import N using (_--_)", "open import H", "",
                 "module M where", "", "m : Set₁", "m = h")
    files = {**HEAVY, "N": leaf("N"), "M": mid, "A": barrel("A", "M")}
    report = report_of(files)
    assert report.tree.modules["M"].shape is b.Shape.MODULE
    assert report.tree.graph["M"] == ("N", "H"), report.tree.graph["M"]
    assert gate(files) == ["A → M → H"]


def test_an_import_after_a_layout_keyword_is_reported() -> None:
    private = module("M", "module M where", "private open import H", "m = Set")
    nested = module("A", "module A where", "module _ where open import H public")
    for name, text in (("M", private), ("A", nested)):
        problems = report_of({**HEAVY, name: text}).problems
        assert [p.kind.value for p in problems] == ["unclassified"], problems
        assert "begin a line with it" in problems[0].message


def test_a_name_beginning_with_a_clause_keyword_is_not_a_clause() -> None:
    text = module("A", "module A where", "open import H", "as-set : Set₁", "as-set = Set")
    report = report_of({**HEAVY, "A": text})
    assert report.tree.modules["A"].shape is b.Shape.MODULE and report.problems == ()


def test_bare_parameters_and_a_glued_where() -> None:
    bare = module("A", "module A ℓ {X : Set ℓ} where", "open import H public")
    glued = module("B", "module B (X : Set)where", "open import H public", "module _ where")
    marked = module("C", "module C .(x : Set) @0 {y : Set} where", "open import H public")
    assert gate({**HEAVY, "A": bare, "B": glued, "C": marked}) == ["A → H", "B → H", "C → H"]


def test_a_telescope_that_is_not_parameters_makes_a_module() -> None:
    assert shape("A", module("A", "module A x : Set where", "open import H public")) \
        is b.Shape.MODULE


def test_plain_agda_modules_are_read() -> None:
    plain = ("{-# OPTIONS --without-K --exact-split --safe #-}\n"
             "module A where\n\nopen import H public\n")
    tree = b.scan_tree(ROOT, [(ROOT / "A.agda", plain), (ROOT / "H.lagda.md", HEAVY["H"])])
    assert tree.modules["A"].shape is b.Shape.BARREL and tree.problems == ()
    report = b.check(tree, frozenset(tree.modules), (ROOT / "Everything.agda",), False)
    assert [" → ".join(p.chain) for p in report.problems] == ["A → H"]


# --------------------------------------------------------------------------- #
# Blind spots: counted, printed, and failing
# --------------------------------------------------------------------------- #

def test_header_name_mismatch_is_unclassified() -> None:
    report = report_of({"A": module("A", "module B where", "open import Data.Nat.Base public")})
    assert kinds(report) == ["unclassified"], kinds(report)
    assert "declares `B`" in report.problems[0].message


def test_missing_header_is_unclassified() -> None:
    report = report_of({"A": module("A", "open import Data.Nat.Base public")})
    assert kinds(report) == ["unclassified"], kinds(report)
    assert "no top-level module header" in report.problems[0].message


def test_unparsed_import_is_unclassified() -> None:
    # The path on a line of its own at the statement's column is no
    # continuation, by the layout rule; Agda refuses it, and so does the gate.
    text = module("A", "module A where", "open import", "A.B public")
    report = report_of({"A": text, "A.B": leaf("A.B")})
    assert "unclassified" in kinds(report), kinds(report)
    assert any("parser cannot read" in p.message for p in report.problems)


def test_no_front_matter_is_unclassified() -> None:
    text = "n" + leaf("A", heavy=True)
    report = report_of({"A": text})
    assert kinds(report) == ["unclassified"]
    assert not report.tree.modules["A"].marked


def test_unresolved_library_import_is_unclassified() -> None:
    report = report_of({"A": leaf("A", "A.Gone"), "A.B": leaf("A.B")})
    assert kinds(report) == ["unclassified"]
    assert "A.Gone" in report.problems[0].message


def test_standard_library_import_is_outside_the_tree() -> None:
    report = report_of({"A": leaf("A", "Data.Nat.Base", "Relation.Binary")})
    assert report.problems == ()


def test_every_misspelling_of_the_marker_is_reported() -> None:
    spellings = ["check_cost: heavy", "Check-Cost: heavy", "check cost: heavy",
                 "  check-cost: heavy", '"check-cost": heavy', "check–cost: heavy"]
    for index, line in enumerate(spellings):
        name = f"M{index}"
        report = report_of({name: module(name, f"module {name} where", "x = Set",
                                         extra=line + "\n")})
        assert kinds(report) == ["marker"], (line, kinds(report))
        assert not report.tree.modules[name].marked
    quoted = module("Q", "module Q where", "x = Set", extra='check-cost: "heavy"\n')
    assert report_of({"Q": quoted}).tree.modules["Q"].marked


def test_unknown_marker_value_and_misspelled_key() -> None:
    odd = module("A", "module A where", "x = Set", extra="check-cost: slow\n")
    typo = module("B", "module B where", "x = Set", extra="check_cost: heavy\n")
    report = report_of({"A": odd, "B": typo})
    assert sorted(kinds(report)) == ["marker", "marker"], kinds(report)
    assert not report.tree.modules["B"].marked
    lines = {p.path.name: p.line for p in report.problems}
    assert lines == {"A.lagda.md": 6, "B.lagda.md": 6}, lines


# --------------------------------------------------------------------------- #
# The gate
# --------------------------------------------------------------------------- #

def test_clean_tree_has_no_problems() -> None:
    files = dict(A5)
    files["Examples.Classical.Groups"] = barrel(
        "Examples.Classical.Groups", "Examples.Classical.Groups.Cyclic", public=False)
    report = report_of(files)
    assert report.problems == (), [p.render() for p in report.problems]
    assert set(report.through) == {"Examples.Classical.Groups.A5"}


def test_every_barrel_above_the_heavy_module_fails() -> None:
    report = report_of(A5)
    failing = sorted(p.chain[0] for p in report.problems)
    assert failing == ["Examples", "Examples.Classical", "Examples.Classical.Groups",
                       "agda-algebras"], failing
    groups = next(p for p in report.problems if p.chain[0] == "Examples.Classical.Groups")
    assert groups.chain == ("Examples.Classical.Groups", "Examples.Classical.Groups.A5",
                            "Examples.Classical.Groups.A5.Tables"), groups.chain
    # The line is the import's, in the barrel's own file.
    text = A5["Examples.Classical.Groups"].split("\n")
    assert "Groups.A5" in text[groups.line - 1], (groups.line, text[groups.line - 1])
    assert "reaches the heavy module" in groups.message


def test_barrel_importing_a_marked_module_directly() -> None:
    files = {"A": barrel("A", "A.H"), "A.H": leaf("A.H", heavy=True)}
    (problem,) = report_of(files).problems
    assert problem.chain == ("A", "A.H") and "is heavy" in problem.message


def test_ordinary_module_may_import_a_heavy_one() -> None:
    files = {"A": leaf("A", "A.H"), "A.H": leaf("A.H", heavy=True)}
    report = report_of(files)
    assert report.problems == ()
    assert report.through == {"A": ("A", "A.H")}


def test_shortest_chain_is_reported() -> None:
    files = {"A": barrel("A", "A.Long"),
             "A.Long": leaf("A.Long", "A.Mid", "A.H"),
             "A.Mid": leaf("A.Mid", "A.H"),
             "A.H": leaf("A.H", heavy=True)}
    (problem,) = report_of(files).problems
    assert problem.chain == ("A", "A.Long", "A.H"), problem.chain


def test_the_first_of_two_shortest_chains_in_source_order() -> None:
    files = {"A": barrel("A", "A.X", "A.Y"), "A.X": leaf("A.X", "A.H"),
             "A.Y": leaf("A.Y", "A.H"), "A.H": leaf("A.H", heavy=True)}
    assert [p.chain for p in report_of(files).problems] == [
        ("A", "A.X", "A.H"), ("A", "A.Y", "A.H")]
    files["A"] = barrel("A", "A.Z")
    files["A.Z"] = leaf("A.Z", "A.Y", "A.X")
    (problem,) = report_of(files).problems
    assert problem.chain == ("A", "A.Z", "A.Y", "A.H"), problem.chain


def test_a_cycle_terminates() -> None:
    files = {"A": barrel("A", "A.X"), "A.X": leaf("A.X", "A.Y"), "A.Y": leaf("A.Y", "A.X")}
    assert report_of(files).problems == ()


def test_legacy_barrels_are_reported_unless_gated() -> None:
    files = {"Legacy.Base": barrel("Legacy.Base", "Legacy.Base.H"),
             "Legacy.Base.H": leaf("Legacy.Base.H", heavy=True)}
    reported = report_of(files)
    assert reported.problems == () and len(reported.notes) == 1
    gated = report_of(files, legacy=True)
    assert kinds(gated) == ["barrel"] and gated.notes == ()


def test_marked_module_missing_from_the_aggregators() -> None:
    files = {"A": leaf("A", heavy=True), "B": leaf("B")}
    report = report_of(files, built=frozenset({"B"}))
    (problem,) = report.problems
    assert problem.kind is b.Kind.BUILD and problem.line == 6, problem
    assert report_of(files, built=frozenset({"A", "B"})).problems == ()


def test_a_marked_module_in_either_aggregator_is_built() -> None:
    files = {"Legacy.Base.H": leaf("Legacy.Base.H", heavy=True), "B": leaf("B")}
    tree = tree_of(files)
    report = b.check(tree, b.aggregated("import B\n") | b.aggregated("import Legacy.Base.H\n"),
                     (ROOT / "Everything.agda", ROOT / "EverythingLegacy.agda"), False)
    assert report.problems == ()


def test_aggregated_reads_the_generated_file() -> None:
    text = "{-# OPTIONS --without-K --safe #-}\n\nmodule Everything where\n\nimport A\nimport A.B\n"
    assert b.aggregated(text) == frozenset({"A", "A.B"})


# --------------------------------------------------------------------------- #
# The audit
# --------------------------------------------------------------------------- #

PROFILE = """Checking Everything (/x/src/Everything.agda).
Total                                              61,838ms
Miscellaneous                                       5,634ms
Examples.Classical.Groups.A5.Tables                 5,242ms
Examples.Classical.Groups.A5                        2,608ms
Examples.Classical.Groups.Cyclic                       10ms

Module throughput:
  Examples.Classical.Groups.A5.Tables (502 lines, 96 lines/s)
"""


def test_profile_times_parses_the_table() -> None:
    times = b.profile_times(PROFILE).unwrap()
    assert dict(times) == {"Examples.Classical.Groups.A5.Tables": 5.242,
                           "Examples.Classical.Groups.A5": 2.608,
                           "Examples.Classical.Groups.Cyclic": 0.01}, dict(times)


def test_profile_times_reads_the_last_table_to_its_end() -> None:
    earlier = "Total  9,000ms \nA  8,000ms \n\n"
    times = b.profile_times(earlier + PROFILE).unwrap()
    assert "A" not in times and len(times) == 3, dict(times)


def test_profile_times_needs_a_total_row() -> None:
    assert b.profile_times("Checking A (/x/A.agda).\n").is_err


def test_audit_lists_both_directions() -> None:
    files = dict(A5)
    files["Examples.Classical.Groups.Cyclic"] = leaf("Examples.Classical.Groups.Cyclic",
                                                     heavy=True)
    tree = tree_of(files)
    times = {"Examples.Classical.Groups.A5.Tables": 5.2, "Examples.Classical.Groups.A5": 3.0,
             "Examples.Classical.Groups.Cyclic": 0.5, "Everything": 0.1}
    result = b.audit(tree, [times], 3.0)
    assert result.unmarked_over == (("Examples.Classical.Groups.A5", 3.0),), result
    assert result.marked_under == (("Examples.Classical.Groups.Cyclic", 0.5),)
    assert result.marked_absent == () and result.outside == 1
    # The line is inclusive: 3.0 s is over it, and a marked module at it is not under.
    at_line = b.audit(tree, [{"Examples.Classical.Groups.Cyclic": 3.0}], 3.0)
    assert at_line.marked_under == () and at_line.marked_absent == (
        "Examples.Classical.Groups.A5.Tables",), at_line
    order = b.audit(tree, [{"Examples.Classical.Groups.A5": 4.0,
                            "Examples.Classical.Groups.A5.Tables": 1.0,
                            "Examples": 9.0, "agda-algebras": 9.0}], 3.0)
    assert [n for n, _ in order.unmarked_over] == [
        "Examples", "agda-algebras", "Examples.Classical.Groups.A5"], order
    lines = b.render_audit(result, [Path("p.log")], tree, b.heavy_through(tree))
    assert any("heavy already, through `Examples.Classical.Groups.A5.Tables`" in line
               for line in lines), lines


def test_least_times_takes_each_modules_minimum() -> None:
    runs = [{"A": 4.6, "B": 2.4}, {"A": 2.9, "B": 5.4, "C": 0.2}, {"A": 4.4}]
    assert dict(b.least_times(runs)) == {"A": 2.9, "B": 2.4, "C": 0.2}
    tree = tree_of({"A": leaf("A"), "B": leaf("B"), "C": leaf("C")})
    assert b.audit(tree, runs, 3.0).unmarked_over == ()
    assert b.audit(tree, runs[:1], 3.0).unmarked_over == (("A", 4.6),)


# --------------------------------------------------------------------------- #
# The command line: exit statuses
# --------------------------------------------------------------------------- #

def _write(root: Path, files: dict[str, str]) -> None:
    for name, text in files.items():
        path = root / (name.replace(".", "/") + ".lagda.md")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
    (root / "Everything.agda").write_text(
        "module Everything where\n\n" + "".join(f"import {n}\n" for n in sorted(files)),
        encoding="utf-8")
    (root / "EverythingLegacy.agda").write_text("module EverythingLegacy where\n",
                                                encoding="utf-8")


def _main(*argv: str) -> tuple[int, str]:
    out = io.StringIO()
    with redirect_stdout(out), redirect_stderr(out):
        status = b.main(list(argv))
    return status, out.getvalue()


def test_the_command_line_surface() -> None:
    files = {"Legacy.Base": barrel("Legacy.Base", "Legacy.Base.H"),
             "Legacy.Base.H": leaf("Legacy.Base.H", heavy=True),
             "A": barrel("A", "A.B"), "A.B": leaf("A.B"), "C": leaf("C", "Legacy.Base.H")}
    with tempfile.TemporaryDirectory() as scratch:
        root = Path(scratch) / "src"
        _write(root, files)
        status, out = _main(str(root), "--list")
        assert status == 0, out
        assert "note (Legacy/, reported only): " in out and "chain: Legacy.Base → Legacy.Base.H" in out
        assert "Barrels, gated (1):\n  A  (1 import, re-exports all)" in out, out
        assert "Barrels in Legacy/, reported only (1):" in out
        assert "Heavy through imports (2):\n  C  (C → Legacy.Base.H)\n  Legacy.Base  (" in out, out
        assert out.rstrip().endswith(
            "2 barrels (1 gated, 1 in Legacy/ reported only), 0 header-only; "
            "1 marked heavy, 2 heavy through imports; 0 problems (0 barrel, 0 build, "
            "0 marker, 0 cannot classify)."), out
        status, out = _main(str(root), "--include-legacy")
        assert status == 1 and "barrel `Legacy.Base` imports `Legacy.Base.H`" in out, out
        status, out = _main(str(root), "--json")
        record = json.loads(out)
        assert status == 0 and record["marked"] == ["Legacy.Base.H"], record
        assert [x["module"] for x in record["barrels"]] == ["A", "Legacy.Base"]
        assert record["heavy_through_imports"]["C"] == ["C", "Legacy.Base.H"]
        assert len(record["notes"]) == 1 and record["problems"] == []
        log = Path(scratch) / "p.log"
        log.write_text("Total  9,000ms \nA.B  2,500ms \n", encoding="utf-8")  # noqa: E501
        status, out = _main(str(root), "--audit", str(log), "--threshold", "2")
        assert status == 0 and "unmarked, at or over 2 s:\n    A.B  2.50 s" in out, out


def test_an_unreadable_module_is_an_io_error() -> None:
    with tempfile.TemporaryDirectory() as scratch:
        root = Path(scratch) / "src"
        _write(root, {"A": leaf("A")})
        locked = root / "A.lagda.md"
        locked.chmod(0)
        try:
            status, out = _main(str(root))
        finally:
            locked.chmod(0o644)
        if os.access(locked, os.R_OK) and status == 0:
            return                       # running as root: nothing is unreadable
        assert status == 2 and out.count(str(locked)) == 1, out


def test_exit_statuses() -> None:
    with tempfile.TemporaryDirectory() as scratch:
        clean, dirty = Path(scratch) / "clean", Path(scratch) / "dirty"
        _write(clean, {"A": barrel("A", "A.B"), "A.B": leaf("A.B"), "A.H": leaf("A.H", heavy=True)})
        _write(dirty, {"A": barrel("A", "A.H"), "A.H": leaf("A.H", heavy=True)})
        status, out = _main(str(clean))
        assert status == 0, out
        status, out = _main(str(dirty))
        assert status == 1 and "chain: A → A.H" in out, out
        assert _main(str(dirty), "--exit-zero")[0] == 0
        assert _main(str(Path(scratch) / "absent"))[0] == 2
        assert _main(str(clean), "--everything", str(Path(scratch) / "none.agda"))[0] == 2
        log = Path(scratch) / "profile.log"
        log.write_text("Total  3,000ms \nA.H  2,000ms \n", encoding="utf-8")
        status, out = _main(str(clean), "--audit", str(log))
        assert status == 0 and "A.H  2.00 s" in out, out
        slower = Path(scratch) / "slower.log"
        slower.write_text("Total  9,000ms \nA.B  3,500ms \nA.H  6,000ms \n", encoding="utf-8")
        status, out = _main(str(clean), "--audit", str(log), str(slower))
        assert status == 0 and "2 logs" in out and "A.B  3.50 s" in out, out
        assert "A.H  2.00 s" in out, out
        assert _main(str(clean), "--audit", str(Path(scratch) / "none.log"))[0] == 2


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
