#!/usr/bin/env python3
"""
File: scripts/python/span_classes.py

Description: Validate the kramdown attribute spans on inline Agda names in the
  corpus's prose against Agda's own classification (issue #553).

  Every Agda name in the rendered prose is marked up with a kramdown attribute
  span, `` `Algebra`{.AgdaRecord} ``, whose class becomes the CSS class that
  colours it (mkdocs.yml's attr_list).  Nothing else checks that the class is
  the *right* one: a Σ-type alias marked ``{.AgdaRecord}`` renders as a record
  though Agda considers it a function, and a ``data`` marked ``{.AgdaFunction}``
  renders as a function though Agda considers it a datatype.  The wrong class is
  invisible to ``mkdocs build --strict`` and to every other gate.

  The ground truth is Agda's own HTML backend.  ``agda --html
  --html-highlight=code`` (``make agda-md``) renders each literate module to
  ``.agda-html/md/<Module>.md``, wrapping every code token in an anchor whose
  ``class`` attribute is Agda's classification of the name at that occurrence,
  resolved in the scope of *that file*.  That resolution is what a name table
  cannot do (the issue's main finding): a ``Lattice`` that is the stdlib record
  in one file and an unrelated alias in another is told apart, and bound
  variables, fields and constructors come out right by construction.  Prose
  passes through the render verbatim, spans and all, so the two sides join on
  (module, name):

  +  the source scan yields every `` `name`{.AgdaX} `` span in the prose
     (outside code fences and HTML comments);
  +  the render scan yields, per module, the set of aspects Agda assigns each
     name in the code (``Operator`` / ``DottedPattern`` modifiers dropped);
  +  a span whose claimed class maps to a different aspect than the one Agda
     assigns the name in that module is reported as a disagreement.

  Three blind spots are tallied, never silently dropped (the corpus-linter
  convention): names that never occur in the module's code (unresolved: a
  name prose mentions but the code never uses), names Agda classifies
  inconsistently within one module (ambiguous: a bound variable shadowing
  a top-level name, where no per-file answer exists), and names whose Agda
  aspect has no span-class counterpart (``Postulate``, ``Primitive``), where a
  class comparison cannot say whether the markup is wrong.

Usage::

    make agda-md          # produce the renders the checker diffs against
    python3 scripts/python/span_classes.py                 # check src/
    python3 scripts/python/span_classes.py --tallies       # list the blind spots
    python3 scripts/python/span_classes.py src/Setoid      # check one subtree

Exit status is 0 when no span disagrees, 1 when one does or when the run could
not measure (an unreadable file, a module with no render).

Design Principles:
  Pure core, effectful shell.  Span extraction, render parsing and the verdict
  are total functions of the two texts; reading files, printing and exit codes
  happen only in ``main`` and its immediate helpers.
"""
from __future__ import annotations

import argparse
import html
import re
import sys
import time
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Optional

# Import the shared utilities the way the sibling scripts do: make this file's
# directory importable, then pull in the Result-returning file reader and the
# literate front end's file discovery.
_SCRIPT_DIR = Path(__file__).resolve().parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))

from _utils.file_ops import read_text  # noqa: E402
from _utils.literate import gather_files  # noqa: E402


# =============================================================================
# The two vocabularies, and the map between them
# =============================================================================

# The span classes the corpus writes (`` `name`{.AgdaX} ``) and the aspect
# Agda's HTML backend emits for the same kind of name.  Agda compounds its
# aspects with the modifiers ``Operator`` (a mixfix/operator name) and
# ``DottedPattern``; the modifiers carry no information the span classes
# distinguish, so they are dropped before comparing.
SPAN_TO_ASPECT = {
    "AgdaFunction": "Function",
    "AgdaRecord": "Record",
    "AgdaDatatype": "Datatype",
    "AgdaInductiveConstructor": "InductiveConstructor",
    "AgdaField": "Field",
    "AgdaModule": "Module",
    "AgdaBound": "Bound",
    "AgdaGeneralizable": "Generalizable",
    "AgdaKeyword": "Keyword",
    "AgdaPrimitiveType": "PrimitiveType",
    "AgdaSymbol": "Symbol",
    "AgdaArgument": "Argument",
}

_ASPECT_MODIFIERS = frozenset({"Operator", "DottedPattern"})


# =============================================================================
# Source side: the kramdown attribute spans in a module's prose
# =============================================================================

@dataclass(frozen=True)
class Span:
    """One `` `name`{.AgdaX} `` occurrence in a module's prose."""
    line: int     # 1-based, into the .lagda.md source
    column: int   # 1-based character column of the opening backtick
    name: str     # the code span's content
    claimed: str  # the AgdaX class the span claims


# A fenced code block (any info string: spans inside a ```text block are no
# more prose than those inside ```agda).
_FENCE = re.compile(r"^\s*(```|~~~)")

# An attribute list immediately after a code span: {.AgdaFunction} and, in
# principle, other kramdown attributes ({#id}, {.class key="val"}).  Only a
# single Agda-prefixed class is the corpus's markup; anything else either is
# not an attribute list at all (set-builder `{ x | … }` left after a span) or
# is counted as unusual rather than silently parsed by a rule of our own.
_ATTR = re.compile(r"\{([^{}]*)\}")
_ATTR_CLASS = re.compile(r"\.([A-Za-z][\w-]*)")


def code_spans(line: str) -> tuple[tuple[int, int, str], ...]:
    """The inline code spans of one prose line: ``(start, end, content)`` with
    ``end`` one past the closing backticks.

    CommonMark's rule: a run of N backticks opens a span closed by the next
    run of exactly N; runs of other lengths in between are content, and an
    opener with no matching closer renders literally (so the scan resumes
    after it).  The N > 1 form is the corpus's idiom for a name containing a
    backtick (`` ``V'`{.AgdaFunction}`` ``).
    """
    out: list[tuple[int, int, str]] = []
    i, n = 0, len(line)
    while i < n:
        if line[i] != "`":
            i += 1
            continue
        j = i
        while j < n and line[j] == "`":
            j += 1
        ticks = j - i
        # Scan for a closing run of exactly `ticks` backticks.
        k = j
        while k < n:
            if line[k] != "`":
                k += 1
                continue
            m = k
            while m < n and line[m] == "`":
                m += 1
            if m - k == ticks:
                break
            k = m  # a run of a different length is content; keep scanning
        if k >= n:
            i = j  # never closed: the opener renders literally
            continue
        out.append((i, k + ticks, line[j:k]))
        i = k + ticks
    return tuple(out)


def span_at(line: str, start: int, end: int, content: str,
            lineno: int) -> tuple[Optional[Span], Optional[tuple[int, str]]]:
    """The Agda span this code span begins, if an attribute list follows it.

    Returns either a ``Span`` or a ``(lineno, reason)`` anomaly: an attribute
    list that mentions an Agda class but is not exactly one ``.AgdaX`` class
    (a shape the checker declines to interpret).  Attribute lists without an
    Agda class are not the corpus's markup and yield neither.
    """
    match = _ATTR.match(line, end)
    if not match:
        return None, None
    classes = _ATTR_CLASS.findall(match.group(1))
    agda = [c for c in classes if c.startswith("Agda")]
    if not agda:
        return None, None
    if match.group(1).strip() == f".{agda[0]}" and len(agda) == 1:
        return Span(line=lineno, column=start + 1, name=content.strip(),
                    claimed=agda[0]), None
    return None, (lineno, match.group(0))


def spans_in_text(text: str) -> tuple[tuple[Span, ...], tuple[tuple[int, str], ...]]:
    """Every Agda attribute span in a module's prose, plus anomalies.

    Fenced code and HTML comments render literally (or not at all), so spans
    there are not markup; both are skipped, threading the two states across
    lines.  Commented-out text is blanked *length-preservingly* — never
    removed — so a column in the report is the column in the source even on a
    line that carries a comment, and prose following a mid-line ``-->`` is
    still scanned (the shape of ``_utils.literate.visible_prose``).
    """
    spans: list[Span] = []
    anomalies: list[tuple[int, str]] = []
    in_fence = False
    in_comment = False
    for lineno, line in enumerate(text.splitlines(), 1):
        if in_comment:
            close = line.find("-->")
            if close < 0:
                continue
            in_comment = False
            line = " " * (close + 3) + line[close + 3:]
        if _FENCE.match(line):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        # Blank fully-closed comments in place; a comment that opens and does
        # not close swallows the rest of the line.
        line = re.sub(r"<!--.*?-->", lambda m: " " * len(m.group(0)), line)
        if "<!--" in line:
            in_comment = True
            line = line[: line.index("<!--")]
        for start, end, content in code_spans(line):
            span, anomaly = span_at(line, start, end, content, lineno)
            if span is not None:
                spans.append(span)
            if anomaly is not None:
                anomalies.append(anomaly)
    return tuple(spans), tuple(anomalies)


# =============================================================================
# Render side: the aspects Agda assigns each name in a module
# =============================================================================

# An anchor with a class attribute and non-empty text, e.g.
# ``<a id="3439" href="Examples.Setoid.HSPCommutativeMonoid.html#3439"
# class="Datatype">𝒦₀</a>``.  Binding markers (``<a id="𝒦₀"></a>``) carry no
# class and never match; prose passes through verbatim and has no anchors.
_ANCHOR = re.compile(r"<a\b[^>]*?\bclass=\"([^\"]+)\"[^>]*>([^<\n]*)</a>")


def aspect_of(class_attr: str) -> Optional[str]:
    """The base aspect of an Agda ``class`` attribute, modifiers dropped:
    ``"Function Operator"`` -> ``Function``, ``"DottedPattern Bound"`` ->
    ``Bound``.  ``None`` when nothing is left, which the corpus never asks
    about and the tally counts rather than guesses."""
    words = [w for w in class_attr.split() if w not in _ASPECT_MODIFIERS]
    return words[0] if len(words) == 1 else None


def render_aspects(text: str) -> tuple[dict[str, frozenset[str]], int]:
    """``name -> aspects`` for every anchor in a rendered module, plus the
    count of anchors whose class attribute reduced to nothing.

    Names are HTML-unescaped (``_&lt;_`` is the operator ``_<_``).  A name
    occurring with more than one aspect in one module is genuinely ambiguous
    (a bound variable shadowing a top-level definition), and the join abstains
    on it rather than picking an occurrence.
    """
    acc: dict[str, set[str]] = {}
    dropped = 0
    for match in _ANCHOR.finditer(text):
        name = html.unescape(match.group(2))
        aspect = aspect_of(match.group(1))
        if aspect is None:
            dropped += 1
        elif name:
            acc.setdefault(name, set()).add(aspect)
    return {name: frozenset(aspects) for name, aspects in acc.items()}, dropped


# =============================================================================
# The join: does the claimed class agree with Agda's aspect?
# =============================================================================

class Verdict(Enum):
    """How one span fared against the render.  Only DISAGREEMENT and
    UNKNOWN_CLASS are failures; the rest are the tallied blind spots."""
    OK = "ok"
    DISAGREEMENT = "disagreement"
    UNKNOWN_CLASS = "unknown span class"
    UNRESOLVED = "unresolved"
    AMBIGUOUS = "ambiguous"
    NO_COUNTERPART = "no span-class counterpart"


_ASPECT_VALUES = frozenset(SPAN_TO_ASPECT.values())

# The two compatibilities the join grants beyond an exact aspect match, each
# because Agda draws a distinction the prose classes do not carry:
#
# +  LOCAL: AgdaBound, AgdaGeneralizable and AgdaArgument all mark a *local*
#    name, while Agda splits locals by syntactic role: λ/∀-bound (Bound),
#    named-argument site (Argument), generalizable variable (Generalizable).
#    Prose says "a local name"; any reading of it is local whenever every
#    aspect the name carries in the module is.  (Issue #553's AgdaBound
#    analysis: marking a bound occurrence `.AgdaBound` is correct even where a
#    like-named global exists, and here no global reading is even in scope.)
# +  RECORD/MODULE: a record declaration gives its name two aspects, the type
#    (Record) and the module Agda spawns with it (Module), so a file that both
#    opens the module and mentions the type yields {Module, Record}.  Both are
#    one declaration, so the sibling aspect may *accompany* the claimed one —
#    but the claimed aspect itself must be present: a name that is only ever a
#    module here does not justify `.AgdaRecord` (the issue's `Lattice-Order`
#    defect class), nor a bare record `.AgdaModule`.
_LOCAL_CLAIMS = frozenset({"AgdaBound", "AgdaGeneralizable", "AgdaArgument"})
_LOCAL_ASPECTS = frozenset({"Bound", "Argument", "Generalizable"})
_RECORD_MODULE_CLAIMS = frozenset({"AgdaRecord", "AgdaModule"})
_RECORD_MODULE_ASPECTS = frozenset({"Record", "Module"})


def verdict_of(span: Span, aspects: Optional[frozenset[str]]) -> Verdict:
    """Classify one span against the aspects its name carries in the render."""
    if span.claimed not in SPAN_TO_ASPECT:
        return Verdict.UNKNOWN_CLASS
    if aspects is None:
        return Verdict.UNRESOLVED
    expected = SPAN_TO_ASPECT[span.claimed]
    if aspects == frozenset({expected}):
        return Verdict.OK
    if (span.claimed in _LOCAL_CLAIMS
            and aspects <= _LOCAL_ASPECTS):
        return Verdict.OK
    # The claimed aspect must be among the name's aspects: a plain module
    # (aspects {Module}) does not justify an `.AgdaRecord` claim — that is the
    # issue's `Lattice-Order` defect class — nor a bare record an
    # `.AgdaModule` one.  The sibling aspect is *allowed* (a record and its
    # spawned module are one declaration), never sufficient alone.
    if (span.claimed in _RECORD_MODULE_CLAIMS
            and SPAN_TO_ASPECT[span.claimed] in aspects
            and aspects <= _RECORD_MODULE_ASPECTS):
        return Verdict.OK
    if len(aspects) != 1:
        return Verdict.AMBIGUOUS
    if next(iter(aspects)) not in _ASPECT_VALUES:
        return Verdict.NO_COUNTERPART
    return Verdict.DISAGREEMENT


# =============================================================================
# Files:  module name <-> render path
# =============================================================================

def module_name_of(path: Path) -> Optional[str]:
    """``src/Examples/Setoid/HSPCommutativeMonoid.lagda.md`` ->
    ``Examples.Setoid.HSPCommutativeMonoid``.  The module name is the path
    below ``src/``; a file outside any ``src`` root has none."""
    parts = path.as_posix().split("/")
    if "src" not in parts or not parts[-1].endswith(".lagda.md"):
        return None
    below = parts[parts.index("src") + 1:]
    return ".".join([*below[:-1], below[-1][: -len(".lagda.md")]])


# =============================================================================
# The allowlist: legitimate markup the checker cannot tell apart, recorded
# =============================================================================

@dataclass(frozen=True)
class AllowlistEntry:
    """One disagreement the checker must keep reporting but not gate on, with
    the reason it is legitimate.  The key is ``(path, name, claimed, actual)``;
    ``reason`` is required so that an entry is never silent."""
    path: str
    name: str
    claimed: str
    actual: str
    reason: str


def parse_allowlist(text: str) -> tuple[AllowlistEntry, ...]:
    """The allowlist file: tab-separated ``path  name  claimed  actual
    reason``, one entry per line, ``#`` comments and blank lines skipped.
    (Tabs because an Agda name never contains one.)"""
    rows = []
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        cells = tuple(c.strip() for c in line.split("\t"))
        rows.append(cells)
    return tuple(AllowlistEntry(*cells)
                 for cells in rows
                 if len(cells) == 5)


def parse_allowlist_checked(text: str) -> tuple[tuple[AllowlistEntry, ...], tuple[str, ...]]:
    """``parse_allowlist`` plus the malformed lines, so a mistyped row fails
    the run rather than silently not matching."""
    good = parse_allowlist(text)
    bad = tuple(line for line in text.splitlines()
                if line.strip() and not line.strip().startswith("#")
                and len(tuple(c.strip() for c in line.split("\t"))) != 5)
    return good, bad


# =============================================================================
# Report
# =============================================================================

@dataclass(frozen=True)
class Finding:
    """One span and how it fared, for the report."""
    path: Path
    span: Span
    verdict: Verdict
    actual: str  # Agda's aspect, or a description when there is none


def analyze(path: Path, text: str,
            renders: dict[str, tuple[dict[str, frozenset[str]], int]]
            ) -> tuple[tuple[Finding, ...], tuple[tuple[int, str], ...], Optional[str]]:
    """The findings for one module: each span's verdict, plus anomalies.

    Returns ``(findings, anomalies, error)``; the error is set (and the rest
    empty) when the module has no render to diff against."""
    module = module_name_of(path)
    if module is None:
        return (), (), f"cannot derive a module name from {path}"
    if module not in renders:
        return (), (), f"{path}: no render at {module}.md (run `make agda-md`)"
    aspects, _ = renders[module]
    spans, anomalies = spans_in_text(text)
    findings = tuple(
        Finding(path=path, span=span, verdict=v,
                actual=(next(iter(a)) if (a := aspects.get(span.name)) and len(a) == 1
                        else (";".join(sorted(a)) if a else "?")))
        for span in spans
        for v in [verdict_of(span, aspects.get(span.name))])
    return findings, anomalies, None


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="Validate kramdown attribute spans (`name`{.AgdaX}) in the "
                    "corpus's prose against Agda's own classification, read "
                    "from the `agda --html` render (issue #553).")
    parser.add_argument("paths", nargs="*", default=["src"],
                        help="files or directories (default: src)")
    parser.add_argument("--html-dir", default=".agda-html/md", metavar="DIR",
                        help="the `agda --html --html-highlight=code` output "
                             "directory (default: .agda-html/md, written by "
                             "`make agda-md`)")
    parser.add_argument("--include-legacy", action="store_true",
                        help="also scan src/Legacy (frozen; skipped by default)")
    parser.add_argument("--tallies", action="store_true",
                        help="list the blind spots (unresolved, ambiguous, "
                             "no-counterpart), not just their counts")
    parser.add_argument("--allowlist", metavar="FILE",
                        default="scripts/python/span_classes.allowlist",
                        help="TSV of recorded legitimate disagreements "
                             "(default: %(default)s, read when it exists).  An "
                             "entry that no longer matches a live disagreement "
                             "fails the run, so the list cannot rot")
    parser.add_argument("--exit-zero", action="store_true",
                        help="always exit 0 (do not signal disagreements)")
    args = parser.parse_args(argv)

    started = time.monotonic()
    html_dir = Path(args.html_dir)
    if not html_dir.is_dir():
        sys.stderr.write(
            f"error: {html_dir} not found; run `make agda-md` first.  The "
            "checker diffs the prose spans against Agda's own render.\n")
        return 2

    files = gather_files([Path(p) for p in args.paths], args.include_legacy)
    if not files:
        sys.stderr.write("error: no .lagda.md files found\n")
        return 2

    # The render side, parsed once per module that has one.
    renders: dict[str, tuple[dict[str, frozenset[str]], int]] = {}
    dropped_anchors = 0
    for render in sorted(html_dir.glob("*.md")):
        text = read_text(render)
        if text.is_err:
            sys.stderr.write(f"error: {render}: {text.unwrap_err()}\n")
            return 1
        aspects, dropped = render_aspects(text.unwrap())
        renders[render.name[: -len(".md")]] = (aspects, dropped)
        dropped_anchors += dropped

    blocked: list[str] = []
    findings: list[Finding] = []
    anomalies: list[tuple[Path, int, str]] = []
    for path in files:
        text = read_text(path)
        if text.is_err:
            blocked.append(f"{path} could not be read: {text.unwrap_err()}")
            continue
        fs, anoms, error = analyze(path, text.unwrap(), renders)
        if error is not None:
            blocked.append(error)
            continue
        findings.extend(fs)
        anomalies.extend((path, lineno, raw) for lineno, raw in anoms)

    elapsed = time.monotonic() - started
    disagreements = [f for f in findings if f.verdict is Verdict.DISAGREEMENT]
    unknown = [f for f in findings if f.verdict is Verdict.UNKNOWN_CLASS]
    tallied = [f for f in findings if f.verdict
               in (Verdict.UNRESOLVED, Verdict.AMBIGUOUS, Verdict.NO_COUNTERPART)]

    # The allowlist: recorded legitimate disagreements.  Matching is exact on
    # (path, name, claimed, actual); an entry that matches nothing is stale
    # (the span was fixed or moved) and fails the run, so the list cannot rot.
    allowlist: tuple[AllowlistEntry, ...] = ()
    allowlist_path = Path(args.allowlist)
    if allowlist_path.is_file():
        allow_text = read_text(allowlist_path)
        if allow_text.is_err:
            blocked.append(f"{allowlist_path} could not be read: "
                           f"{allow_text.unwrap_err()}")
        else:
            entries, malformed = parse_allowlist_checked(allow_text.unwrap())
            allowlist = entries
            blocked.extend(f"{allowlist_path}: malformed allowlist line: {line}"
                           for line in malformed)

    def is_allowlisted(f: Finding) -> Optional[AllowlistEntry]:
        return next((e for e in allowlist
                     if (e.path, e.name, e.claimed, e.actual)
                     == (f.path.as_posix(), f.span.name, f.span.claimed,
                         f.actual)), None)

    allowlisted = [(f, e) for f in disagreements
                   if (e := is_allowlisted(f)) is not None]
    live = [f for f in disagreements if is_allowlisted(f) is None]
    stale = [e for e in allowlist
             if not any(f.span.name == e.name and f.span.claimed == e.claimed
                        and f.actual == e.actual and f.path.as_posix() == e.path
                        for f in disagreements)]
    blocked.extend(f"{allowlist_path}: stale entry (no live disagreement): "
                   f"{e.path} `{e.name}`{{.{e.claimed}}}" for e in stale)

    if live or unknown:
        out = sys.stderr
        out.write(f"✗ {len(live) + len(unknown)} span(s) whose class "
                  "disagrees with Agda's classification:\n\n")
        for f in live:
            out.write(f"  {f.path}:{f.span.line}:{f.span.column}: "
                      f"`{f.span.name}`{{.{f.span.claimed}}}: "
                      f"Agda says {f.actual}\n")
        for f in unknown:
            out.write(f"  {f.path}:{f.span.line}:{f.span.column}: "
                      f"`{f.span.name}`{{.{f.span.claimed}}}: "
                      f"not a span class Agda emits\n")
        out.write("\n")
    else:
        print(f"✓ every resolved span agrees with Agda's classification "
              f"({len(findings)} span(s) in {len(files)} module(s), "
              f"{elapsed:.1f}s).")
    if allowlisted:
        print(f"{len(allowlisted)} disagreement(s) allowlisted as legitimate "
              f"markup (see {allowlist_path}):")
        for f, e in allowlisted:
            print(f"  {f.path}:{f.span.line}: `{f.span.name}`"
                  f"{{.{f.span.claimed}}} (Agda: {f.actual}): {e.reason}")

    counts = {v: sum(1 for f in tallied if f.verdict is v)
                  for v in (Verdict.UNRESOLVED, Verdict.AMBIGUOUS, Verdict.NO_COUNTERPART)}
    print(f"Tallied blind spots (not failures): "
          f"{counts[Verdict.UNRESOLVED]} unresolved (name never occurs in the "
          f"module's code), "
          f"{counts[Verdict.AMBIGUOUS]} ambiguous (more than one aspect in the "
          f"module), "
          f"{counts[Verdict.NO_COUNTERPART]} with an aspect no span class has "
          f"(Postulate, Primitive, …).")
    if dropped_anchors:
        print(f"{dropped_anchors} anchor(s) whose class reduced to nothing "
              f"(skipped).")
    if anomalies:
        print(f"{len(anomalies)} attribute list(s) that are not a single "
              f"`.AgdaX` class (skipped).")
    if args.tallies:
        for v, label in ((Verdict.UNRESOLVED, "unresolved"),
                         (Verdict.AMBIGUOUS, "ambiguous"),
                         (Verdict.NO_COUNTERPART, "no counterpart")):
            members = [f for f in tallied if f.verdict is v]
            if members:
                print(f"\n{label}:")
                for f in members:
                    print(f"  {f.path}:{f.span.line}: `{f.span.name}`"
                          f"{{.{f.span.claimed}}} (Agda: {f.actual})")
    if anomalies and args.tallies:
        print("\nanomalous attribute lists:")
        for path, lineno, raw in anomalies:
            print(f"  {path}:{lineno}: {raw}")

    if blocked:
        sys.stderr.write(
            f"\n✗ the check could not measure {len(blocked)} module(s), so its "
            "count is not trustworthy:\n")
        for reason in blocked[:20]:
            sys.stderr.write(f"  {reason}\n")
        return 1
    if args.exit_zero:
        return 0
    return 1 if live or unknown else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
