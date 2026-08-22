#!/usr/bin/env python3
"""
File: scripts/python/test_docstring_audit.py

Description: Tests for ``docstring_audit.py``.

  Dependency-free: run directly with
  ``python3 scripts/python/test_docstring_audit.py`` (prints a pass count and
  exits 0 on success) or under ``pytest`` if it is installed.  Each scenario is
  a small literate ``.lagda.md`` fragment exercising one decision the analyzer
  makes.

  The analyzer's *definition extraction* was additionally validated against
  Agda itself: for three modules of different shape the set of names it reports
  equals the set ``agda``'s own scope checker reports as the module's exports
  (``Cmd_show_module_contents_toplevel``).  That check needs a type-checker and
  so cannot live here; see the PR for the transcript.
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import docstring_audit as da  # noqa: E402


# --------------------------------------------------------------------------- #
# Fragment helpers
# --------------------------------------------------------------------------- #

def block(*code: str) -> str:
    """Wrap Agda lines in a visible ```` ```agda ```` fence."""
    return "```agda\n" + "\n".join(code) + "\n```\n"


def hidden(*code: str) -> str:
    """Wrap Agda lines in the corpus's hidden ``<!-- … -->`` preamble fence."""
    return "<!--\n" + block(*code) + "-->\n"


def analyze(text: str, path: str = "src/T/M.lagda.md") -> da.FileReport:
    return da.analyze_text(Path(path), text)


def names(text: str) -> list[str]:
    return [d.name for d in analyze(text).definitions]


def statuses(text: str) -> dict[str, str]:
    return {d.name: d.status.value for d in analyze(text).definitions}


# --------------------------------------------------------------------------- #
# Definition extraction: what counts as a public definition
# --------------------------------------------------------------------------- #

def test_top_level_signature() -> None:
    assert names(block("foo : Set", "foo = A")) == ["foo"]


def test_definitions_inside_anonymous_module() -> None:
    # The corpus's dominant idiom: everything indented inside `module _ … where`.
    # A column-0-only detector would find none of these.
    assert names(block(
        "module _ (A : Set) where",
        "  foo : Set",
        "  foo = A",
        "  bar : Set",
        "  bar = A",
    )) == ["foo", "bar"]


def test_private_block_is_not_public() -> None:
    assert names(block(
        "private",
        "  hidden-helper : Set",
        "  hidden-helper = A",
        "visible : Set",
        "visible = A",
    )) == ["visible"]


def test_private_inside_module_closes_at_dedent() -> None:
    assert names(block(
        "module _ where",
        "  private",
        "    helper : Set",
        "    helper = A",
        "  exposed : Set",
        "  exposed = A",
    )) == ["exposed"]


def test_where_body_is_local() -> None:
    assert names(block(
        "foo : Set",
        "foo = helper",
        "  where",
        "  helper : Set",
        "  helper = A",
        "bar : Set",
        "bar = A",
    )) == ["foo", "bar"]


def test_inline_where_does_not_swallow_the_next_definition() -> None:
    # The regression that motivated Frame.opener: an inline `where` opens a
    # block that the *following* sibling must not be absorbed into.
    assert names(block(
        "foo : Set",
        "foo = h  where open M renaming (x to y)",
        "bar : Set",
        "bar = A",
    )) == ["foo", "bar"]


def test_record_fields_are_not_standalone_definitions() -> None:
    assert names(block(
        "record R : Set where",
        "  constructor mkR",
        "  field",
        "    fst : Set",
        "    snd : Set",
        "after : Set",
        "after = A",
    )) == ["R", "after"]


def test_record_members_are_attributed_to_the_record() -> None:
    # A non-field member of a record body is public API, but Markdown cannot be
    # interleaved between record members, so it is the record's prose that
    # documents it.
    assert names(block(
        "record R : Set where",
        "  field f : Set",
        "  derived : Set",
        "  derived = f",
    )) == ["R"]


def test_data_constructors_are_not_standalone_definitions() -> None:
    assert names(block(
        "data D : Set where",
        "  c₁ : D",
        "  c₂ : D → D",
    )) == ["D"]


def test_named_submodule_is_a_definition_and_a_namespace() -> None:
    report = analyze(block(
        "module Sub (A : Set) where",
        "  inner : Set",
        "  inner = A",
    ))
    assert [d.name for d in report.definitions] == ["Sub", "inner"]
    assert [d.qname for d in report.definitions] == ["T.M.Sub", "T.M.Sub.inner"]


def test_anonymous_module_contributes_no_namespace() -> None:
    report = analyze(block("module _ where", "  x : Set", "  x = A"))
    assert report.definitions[0].qname == "T.M.x"


def test_module_application_declares_nothing_new() -> None:
    assert names(block("module N = Sub A")) == []


def test_multi_line_declaration_head() -> None:
    # `where` on a continuation line still opens the block.
    assert names(block(
        "record R (A : Set)",
        "         (B : Set) : Set where",
        "  field f : A",
        "next : Set",
        "next = A",
    )) == ["R", "next"]


def test_where_found_after_a_long_continuation() -> None:
    # Guards the linear-scan optimisation in _logical_items: only the newly
    # added line is searched for `where`, never the accumulated item (which was
    # quadratic and cost 38 s of a 41 s corpus run).  A `where` arriving after
    # many continuation lines must still open its block, so the definition that
    # follows at the outer indent is not swallowed into it.
    long_tail = ["      , item{}".format(i) for i in range(200)]
    assert names(block(
        "module _ where",
        "  table : List Nat",
        "  table = big",
        *long_tail,
        "    where big = []",
        "  after : Set",
        "  after = A",
    )) == ["table", "after"]


def test_two_names_in_one_signature() -> None:
    assert names(block("f g : Set", "f = A", "g = A")) == ["f", "g"]


def test_two_names_in_one_signature_share_a_rank() -> None:
    # `f g : T` is one declaration, so both names share the fence position and
    # therefore the same status.
    text = "Some prose.\n\n" + block("f g : Set", "f = A", "g = A")
    assert statuses(text) == {"f": "documented", "g": "documented"}


def test_private_variable_block() -> None:
    # `private variable` opens two blocks on one line; the level declarations
    # that follow are generalized variables, not definitions.
    assert names(block(
        "private variable",
        "  α β : Level",
        "real : Set",
        "real = A",
    )) == ["real"]


def test_postulate_items_are_public_definitions() -> None:
    assert names(block("postulate", "  ax : Set")) == ["ax"]


def test_imports_and_fixity_are_not_definitions() -> None:
    assert names(block(
        "open import M using ( x )",
        "open M public",
        "import N as O",
        "infixl 6 _+_",
        "syntax f x = x ⟨ f ⟩",
    )) == []


def test_clauses_are_not_definitions() -> None:
    # `with`-clauses and absurd patterns begin with an already-declared name.
    report = analyze(block(
        "f : Set → Set",
        "f x with g x",
        "... | yes p = A",
        "h : ⊥ → Set",
        "h ()",
    ))
    assert [d.name for d in report.definitions] == ["f", "h"]
    assert report.unparsed == ()


def test_mixfix_names() -> None:
    assert names(block("_∘_ : Set", "_∘_ = A", "∣_∣ : Set", "∣_∣ = A")) == ["_∘_", "∣_∣"]


def test_module_header_is_not_a_definition() -> None:
    report = analyze(hidden("module T.M where") + block("x : Set", "x = A"))
    assert [d.name for d in report.definitions] == ["x"]
    assert report.hidden_defs == ()


def test_declarations_in_hidden_fences_are_reported_separately() -> None:
    report = analyze(hidden("module T.M where", "helper : Set", "helper = A")
                     + block("x : Set", "x = A"))
    assert [d.name for d in report.definitions] == ["x"]
    assert [d.name for d in report.hidden_defs] == ["helper"]


def test_comments_inside_fences_are_not_prose() -> None:
    # A `-- |`-style comment is stripped with the rest of the comments; it never
    # counts as the definition's documentation (STYLE_GUIDE § Prose belongs in
    # Markdown).
    assert statuses(block(
        "-- | This looks like a docstring but is not one.",
        "x : Set",
        "x = A",
    )) == {"x": "undocumented"}


def test_commented_out_declaration_is_invisible() -> None:
    assert names(block("{- foo : Set -}", "bar : Set", "bar = A")) == ["bar"]


# --------------------------------------------------------------------------- #
# Prose classification and status
# --------------------------------------------------------------------------- #

def test_paragraph_documents_the_first_definition_only() -> None:
    text = "A real paragraph about foo.\n\n" + block(
        "foo : Set", "foo = A", "bar : Set", "bar = A")
    assert statuses(text) == {"foo": "documented", "bar": "grouped"}


def test_heading_alone_is_not_documentation() -> None:
    text = "#### A heading\n\n" + block("foo : Set", "foo = A")
    assert statuses(text) == {"foo": "heading-only"}


def test_boilerplate_alone_is_not_documentation() -> None:
    text = ("#### Heading\n\nThis is the [T.M][] module of the "
            "[Agda Universal Algebra Library][].\n\n") + block("foo : Set", "foo = A")
    assert statuses(text) == {"foo": "boilerplate"}


def test_boilerplate_plus_real_prose_is_documentation() -> None:
    text = ("This is the [T.M][] module of the [Agda Universal Algebra Library][].\n\n"
            "A semigroup is a set with an associative binary operation.\n\n"
            ) + block("foo : Set", "foo = A")
    assert statuses(text) == {"foo": "documented"}


def test_no_prose_at_all() -> None:
    assert statuses(block("foo : Set", "foo = A")) == {"foo": "undocumented"}


def test_prose_carries_across_a_hidden_fence() -> None:
    # The hidden preamble renders as nothing, so the module's prose sits
    # immediately above the first *visible* code block on the rendered page.
    text = ("#### Heading\n\nA real paragraph.\n\n"
            + hidden("module T.M where") + block("foo : Set", "foo = A"))
    assert statuses(text) == {"foo": "documented"}


def test_front_matter_is_not_prose() -> None:
    text = ('---\nlayout: default\ntitle : "T.M"\n---\n\n'
            + block("foo : Set", "foo = A"))
    assert statuses(text) == {"foo": "undocumented"}


def test_front_matter_does_not_mask_boilerplate() -> None:
    text = ('---\nlayout: default\n---\n\n#### H\n\nThis is the [T.M][] module of '
            'the [Agda Universal Algebra Library][].\n\n'
            + block("foo : Set", "foo = A"))
    assert analyze(text).module_prose is da.Prose.BOILERPLATE


def test_link_definitions_and_rules_are_not_prose() -> None:
    text = "### H\n\n---\n\n[Some.Module]: ./x.md\n\n" + block("foo : Set", "foo = A")
    assert statuses(text) == {"foo": "heading-only"}


def test_each_fence_gets_its_own_prose() -> None:
    text = ("First paragraph.\n\n" + block("foo : Set", "foo = A")
            + "\n#### Just a heading\n\n" + block("bar : Set", "bar = A"))
    assert statuses(text) == {"foo": "documented", "bar": "heading-only"}


def test_module_prose_is_the_prose_before_the_first_fence() -> None:
    text = ("#### Heading\n\nReal module prose.\n\n"
            + hidden("module T.M where")
            + "\n#### Section\n\n" + block("foo : Set", "foo = A"))
    assert analyze(text).module_prose is da.Prose.PARAGRAPH


# --------------------------------------------------------------------------- #
# Named coverage: does the prose mention the definition it sits above?
# --------------------------------------------------------------------------- #

def test_named_when_prose_mentions_the_definition() -> None:
    text = "`foo`{.AgdaFunction} is the thing.\n\n" + block("foo : Set", "foo = A")
    assert analyze(text).definitions[0].named


def test_not_named_when_prose_does_not_mention_it() -> None:
    text = "Some general remarks about the theme.\n\n" + block("foo : Set", "foo = A")
    assert not analyze(text).definitions[0].named


def test_named_covers_a_mixfix_written_applied() -> None:
    # `_∘_` is written `∘` in prose; every part must appear.
    text = "Composition `∘` chains two maps.\n\n" + block("_∘_ : Set", "_∘_ = A")
    assert analyze(text).definitions[0].named


def test_named_is_false_without_prose() -> None:
    assert not analyze(block("foo : Set", "foo = A")).definitions[0].named


# --------------------------------------------------------------------------- #
# Usage: is a definition referenced anywhere?
# --------------------------------------------------------------------------- #

def _usage(*pairs: tuple[str, str]):
    """Build a usage index over an ad-hoc corpus of (path, text)."""
    texts = [(Path(p), s) for p, s in pairs]
    reports = [da.analyze_text(p, s) for p, s in texts]
    return da.build_usage_index(texts, reports), reports


def _by_name(reports):
    return {d.name: d for r in reports for d in r.definitions}


def test_used_by_another_module() -> None:
    usage, reports = _usage(
        ("src/T/A.lagda.md", block("foo : Set", "foo = A")),
        ("src/T/B.lagda.md", block("bar : Set", "bar = foo")),
    )
    assert usage.used(_by_name(reports)["foo"])


def test_used_within_its_own_module() -> None:
    usage, reports = _usage(
        ("src/T/A.lagda.md", block("foo : Set", "foo = A", "bar : Set", "bar = foo")),
    )
    assert usage.used(_by_name(reports)["foo"])


def test_self_recursion_is_not_use() -> None:
    usage, reports = _usage(
        ("src/T/A.lagda.md", block("foo : Nat → Set", "foo (suc n) = foo n", "foo zero = A")),
    )
    assert not usage.used(_by_name(reports)["foo"])


def test_definition_referenced_by_nothing_is_unused() -> None:
    usage, reports = _usage(
        ("src/T/A.lagda.md", block("foo : Set", "foo = A")),
        ("src/T/B.lagda.md", block("bar : Set", "bar = B")),
    )
    assert not usage.used(_by_name(reports)["foo"])


def test_mention_in_an_import_list_is_not_use() -> None:
    # `open import T.A using ( foo )` brings the name in; that is not a use site.
    usage, reports = _usage(
        ("src/T/A.lagda.md", block("foo : Set", "foo = A")),
        ("src/T/B.lagda.md", block("open import T.A using ( foo )", "bar : Set", "bar = B")),
    )
    assert not usage.used(_by_name(reports)["foo"])


def test_ambiguous_names_are_recorded() -> None:
    usage, _ = _usage(
        ("src/T/A.lagda.md", block("dup : Set", "dup = A")),
        ("src/T/B.lagda.md", block("dup : Set", "dup = B")),
    )
    assert "dup" in usage.ambiguous


def test_usage_appears_in_the_harvest_record() -> None:
    usage, reports = _usage(
        ("src/T/A.lagda.md", "Prose about `foo`.\n\n" + block("foo : Set", "foo = A")),
        ("src/T/B.lagda.md", block("bar : Set", "bar = foo")),
    )
    record = da.to_record(_by_name(reports)["foo"], usage)
    assert record["used"] is True
    assert record["named_in_prose"] is True
    assert record["name_is_ambiguous"] is False


# --------------------------------------------------------------------------- #
# Reporting
# --------------------------------------------------------------------------- #

def test_strict_reading_counts_grouped_as_a_gap() -> None:
    text = "A real paragraph.\n\n" + block("foo : Set", "foo = A", "bar : Set", "bar = A")
    report = analyze(text)
    lenient = [d for d in report.definitions if d.status in da.GAP_STATUSES]
    strict = [d for d in report.definitions if d.status in da.STRICT_GAP_STATUSES]
    assert [d.name for d in lenient] == []
    assert [d.name for d in strict] == ["bar"]


def test_tally_groups_by_subtree() -> None:
    a = analyze(block("x : Set", "x = A"), "src/Setoid/A.lagda.md")
    b = analyze(block("y : Set", "y = A"), "src/Classical/B.lagda.md")
    rows = {t.subtree: t.total for t in da.tally([a, b])}
    assert rows == {"Setoid": 1, "Classical": 1}


def test_top_level_module_is_its_own_subtree() -> None:
    r = analyze(block("x : Set", "x = A"), "src/Setoid.lagda.md")
    assert da.subtree_of(r.path) == "(top level)"


def test_harvest_record_joins_on_qname() -> None:
    text = "The prose about foo.\n\n" + block("foo : Set", "foo = A")
    record = da.to_record(analyze(text).definitions[0])
    assert record["qname"] == "T.M.foo"
    assert record["prose"] == "The prose about foo."
    assert record["signature"] == "foo : Set"
    assert record["kind"] == "signature"
    assert record["status"] == "documented"


def test_module_name_from_path() -> None:
    assert da.module_name(Path("src/Setoid/Algebras/Basic.lagda.md")) \
        == "Setoid.Algebras.Basic"


def test_line_numbers_point_into_the_literate_source() -> None:
    text = "Prose line.\n\n" + block("foo : Set", "foo = A")
    # 1: prose, 2: blank, 3: fence opener, 4: the declaration.
    assert analyze(text).definitions[0].line == 4


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
