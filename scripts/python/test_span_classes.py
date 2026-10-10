#!/usr/bin/env python3
"""Tests for ``span_classes.py``.

Dependency-free: run directly with ``python3 scripts/python/test_span_classes.py``
(prints ``OK`` and exits 0 on success) or under ``pytest`` if it is installed.
Each scenario is a small Markdown or render fragment exercising one rule of the
span scanner, the render parser, or the join.  The Agda side is validated
against the real renders in the pull request, not here.
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import span_classes as sc  # noqa: E402


def spans(text: str) -> list[tuple[str, str]]:
    """The (name, claimed class) pairs the scanner sees in ``text``."""
    found, _ = sc.spans_in_text(text)
    return [(s.name, s.claimed) for s in found]


# --------------------------------------------------------------------------- #
# code_spans: the CommonMark code-span rule the scanner relies on.
# --------------------------------------------------------------------------- #
def test_plain_code_span() -> None:
    assert sc.code_spans("see `Algebra` here") == ((4, 13, "Algebra"),)


def test_multi_backtick_span() -> None:
    # A name containing a backtick is fenced with two: the inner single
    # backtick is content, not a closer.
    assert sc.code_spans("``V'`` after") == ((0, 6, "V'"),)


def test_attribute_inside_a_double_backtick_span_is_content() -> None:
    # The corpus documents the markup itself as `` ``Algebra`{.AgdaRecord}`` ``:
    # the attribute list sits inside the code span and is not a span claim.
    assert spans("``Algebra`{.AgdaRecord}``") == []


def test_unterminated_opener_renders_literally() -> None:
    assert sc.code_spans("a `b c") == ()


def test_longer_run_does_not_close() -> None:
    # The closer must be exactly the opener's length; a double-backtick run
    # does not close a single-backtick span.
    assert sc.code_spans("`a `` b` x") == ((0, 8, "a `` b"),)


def test_adjacent_spans_are_separate() -> None:
    # The corpus idiom `S`{.AgdaFunction}` x`: one span for the name, one for
    # the argument.
    assert sc.code_spans("`S`{.AgdaFunction}` x`") == ((0, 3, "S"), (18, 22, " x"),)


# --------------------------------------------------------------------------- #
# spans_in_text: which spans are the checker's business.
# --------------------------------------------------------------------------- #
def test_span_with_class_is_found() -> None:
    assert spans("an `Algebra`{.AgdaRecord} here") == [("Algebra", "AgdaRecord")]


def test_span_without_attribute_is_not() -> None:
    assert spans("a plain `V 𝒦₀` span") == []


def test_non_agda_attribute_is_not() -> None:
    assert spans("math `S`{e} and `{0, 1}` sets") == []


def test_heading_id_attribute_is_not() -> None:
    assert spans("### Heading `x` {#some-id}") == []


def test_spans_skip_fenced_code() -> None:
    text = "prose `A`{.AgdaFunction}\n```agda\nx = `B`{.AgdaFunction}\n```\n"
    assert spans(text) == [("A", "AgdaFunction")]


def test_spans_skip_html_comments() -> None:
    text = "keep `A`{.AgdaFunction}\n<!--\n`B`{.AgdaFunction}\n-->\nkeep `C`{.AgdaRecord}"
    assert spans(text) == [("A", "AgdaFunction"), ("C", "AgdaRecord")]


def test_spans_skip_single_line_comment() -> None:
    assert spans("a <!-- `B`{.AgdaFunction} --> b `C`{.AgdaRecord}") == \
        [("C", "AgdaRecord")]


def test_line_and_column_point_into_source() -> None:
    found, _ = sc.spans_in_text("one\n\ntwo `𝒦₀`{.AgdaDatatype} tail")
    assert [(f.line, f.column) for f in found] == [(3, 5)]


def test_anomaly_on_compound_attribute_with_agda_class() -> None:
    # Not the corpus's single-class markup: tallied as an anomaly, never
    # silently interpreted.
    _, anomalies = sc.spans_in_text("`X`{.AgdaFunction .wide}")
    assert anomalies == ((1, "{.AgdaFunction .wide}"),)


# --------------------------------------------------------------------------- #
# aspect_of / render_aspects: reading Agda's classification out of the render.
# --------------------------------------------------------------------------- #
def test_aspect_drops_modifiers() -> None:
    assert sc.aspect_of("Function Operator") == "Function"
    assert sc.aspect_of("DottedPattern Bound") == "Bound"
    assert sc.aspect_of("Record") == "Record"


def test_aspect_of_empty_residue() -> None:
    assert sc.aspect_of("Operator") is None


def test_render_aspects_collects_and_unescapes() -> None:
    text = ('<a id="9" href="M.html#9" class="Datatype">_&lt;_</a> '
            '<a id="4" href="M.html#4" class="Function Operator">f</a>')
    aspects, dropped = sc.render_aspects(text)
    assert aspects == {"_<_": frozenset({"Datatype"}), "f": frozenset({"Function"})}
    assert dropped == 0


def test_render_aspects_skips_classless_binding_markers() -> None:
    aspects, _ = sc.render_aspects('<a id="𝒦₀"></a><a id="7" class="Datatype">𝒦₀</a>')
    assert aspects == {"𝒦₀": frozenset({"Datatype"})}


def test_render_aspects_keeps_multiple_aspects() -> None:
    text = ('<a id="1" class="Bound">N</a> <a id="2" class="Function">N</a>')
    aspects, _ = sc.render_aspects(text)
    assert aspects == {"N": frozenset({"Bound", "Function"})}


# --------------------------------------------------------------------------- #
# verdict_of: the join's five answers.
# --------------------------------------------------------------------------- #
def mk(name: str, claimed: str) -> sc.Span:
    return sc.Span(line=1, column=1, name=name, claimed=claimed)


def test_agreement() -> None:
    assert sc.verdict_of(mk("f", "AgdaFunction"), frozenset({"Function"})) \
        is sc.Verdict.OK


def test_disagreement() -> None:
    # The issue's 𝒦₀ shape: a datatype claimed as a function.
    assert sc.verdict_of(mk("𝒦₀", "AgdaFunction"), frozenset({"Datatype"})) \
        is sc.Verdict.DISAGREEMENT


def test_unresolved_when_name_absent_from_code() -> None:
    assert sc.verdict_of(mk("ghost", "AgdaFunction"), None) is sc.Verdict.UNRESOLVED


def test_ambiguous_when_name_carries_two_aspects() -> None:
    assert sc.verdict_of(mk("N", "AgdaBound"), frozenset({"Bound", "Function"})) \
        is sc.Verdict.AMBIGUOUS


def test_no_counterpart_for_aspects_without_a_span_class() -> None:
    # A postulate claimed as a function cannot be judged by class alone.
    assert sc.verdict_of(mk("axiom", "AgdaFunction"), frozenset({"Postulate"})) \
        is sc.Verdict.NO_COUNTERPART


def test_unknown_class_is_a_defect() -> None:
    assert sc.verdict_of(mk("f", "AgdaFunctoin"), frozenset({"Function"})) \
        is sc.Verdict.UNKNOWN_CLASS


def test_local_claims_accept_any_local_aspect() -> None:
    # Prose says "a local name"; Agda splits locals by syntactic role.  The
    # issue's `𝒦` case: a bound variable of the discourse, rendered Argument
    # at a named-argument site in this module.
    assert sc.verdict_of(mk("𝒦", "AgdaBound"), frozenset({"Argument"})) \
        is sc.Verdict.OK
    assert sc.verdict_of(mk("𝑨", "AgdaGeneralizable"), frozenset({"Bound"})) \
        is sc.Verdict.OK
    assert sc.verdict_of(mk("ℓ", "AgdaBound"),
                         frozenset({"Argument", "Bound", "Generalizable"})) \
        is sc.Verdict.OK


def test_local_claim_does_not_cover_a_global_reading() -> None:
    # A name that is bound somewhere and a function elsewhere is genuinely
    # ambiguous: abstain, do not bless.
    assert sc.verdict_of(mk("N", "AgdaBound"), frozenset({"Bound", "Function"})) \
        is sc.Verdict.AMBIGUOUS


def test_record_and_its_module_are_one_declaration() -> None:
    assert sc.verdict_of(mk("FiniteSignature", "AgdaRecord"),
                         frozenset({"Module", "Record"})) is sc.Verdict.OK
    assert sc.verdict_of(mk("IsSubgroup", "AgdaModule"),
                         frozenset({"Module", "Record"})) is sc.Verdict.OK


def test_module_function_mix_stays_ambiguous() -> None:
    assert sc.verdict_of(mk("X", "AgdaRecord"), frozenset({"Module", "Function"})) \
        is sc.Verdict.AMBIGUOUS


# --------------------------------------------------------------------------- #
# The allowlist: recorded legitimate disagreements.
# --------------------------------------------------------------------------- #
def test_parse_allowlist_skips_comments_and_blanks() -> None:
    text = "# comment\n\nsrc/M.lagda.md\t_≟_\tAgdaField\tBound\tthe field, bound here\n"
    entries, bad = sc.parse_allowlist_checked(text)
    assert bad == ()
    assert entries == (sc.AllowlistEntry(
        path="src/M.lagda.md", name="_≟_", claimed="AgdaField",
        actual="Bound", reason="the field, bound here"),)


def test_parse_allowlist_reports_malformed_lines() -> None:
    _, bad = sc.parse_allowlist_checked("src/M.lagda.md\t_missing cells\n")
    assert bad == ("src/M.lagda.md\t_missing cells",)


# --------------------------------------------------------------------------- #
# module_name_of and the end-to-end analyze.
# --------------------------------------------------------------------------- #
def test_module_name_from_path() -> None:
    p = Path("src/Examples/Setoid/HSPCommutativeMonoid.lagda.md")
    assert sc.module_name_of(p) == "Examples.Setoid.HSPCommutativeMonoid"


def test_module_name_outside_src() -> None:
    assert sc.module_name_of(Path("docs/index.md")) is None


def test_analyze_reports_each_span() -> None:
    source = "prose `𝒦₀`{.AgdaFunction} and `in₀`{.AgdaInductiveConstructor}\n"
    render = ('<a id="1" class="Datatype">𝒦₀</a> '
              '<a id="2" class="InductiveConstructor">in₀</a>')
    renders = {"M": sc.render_aspects(render)}
    findings, anomalies, error = sc.analyze(Path("src/M.lagda.md"), source, renders)
    assert error is None and anomalies == ()
    assert [(f.verdict, f.actual) for f in findings] == [
        (sc.Verdict.DISAGREEMENT, "Datatype"), (sc.Verdict.OK, "InductiveConstructor")]


def test_analyze_blocks_a_module_without_render() -> None:
    findings, _, error = sc.analyze(Path("src/M.lagda.md"), "text", {})
    assert findings == () and error is not None and "make agda-md" in error


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
