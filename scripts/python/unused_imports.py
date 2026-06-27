#!/usr/bin/env python3
"""Flag unused ``import`` / ``open`` statements in the Agda corpus.

The library is literate Markdown (``.lagda.md``): Agda code lives inside
```` ```agda ```` fenced blocks.  Every module opens a long list of names from
the standard library and from sibling modules, and over time some of those
names stop being used.  This linter reports names that a module brings into
scope but never references, so they can be pruned by hand.

What it checks
--------------

For each ``.lagda.md`` file it extracts the Agda code, removes comments and
string literals, and classifies every ``import`` / ``open`` statement.  A
statement is reported only when its set of in-scope names is *closed* — that
is, when the textual analysis can see every name it introduces:

  * ``open import M using (a; b; c)``      -> names {a, b, c}
  * ``open import M using () renaming (x to y)``  -> names {y}
  * ``open M using (a) renaming (b to c)`` -> names {a, c}
  * ``open import M as N using (a)``        -> names {N, a}
  * ``import M as N``                        -> name  {N}   (qualified access)
  * ``import M``                             -> the path ``M`` (qualified access)

A name counts as *used* when its token appears anywhere in the module's code
outside the import statements themselves (the module header telescope and the
argument lists of later module applications both count as use sites).  For a
mixfix name such as ``_∙_`` the operator part ``∙`` is what appears at a use
site (``x ∙ y``), so a mixfix name is used when either its full form or any of
its name parts occurs.

What it deliberately does NOT flag
----------------------------------

  * ``public`` re-exports — they exist to be used by *importers*, not locally.
  * ``open import M`` / ``open M`` with no ``using`` (a whole-module open),
    ``hiding (…)``, and bare ``renaming (…)`` — these bring in an open-ended set
    of names that a textual tool cannot enumerate.  They are counted as
    "unanalyzable" and listed only under ``--show-open-ended``.

Soundness
---------

The analysis is tuned to avoid false positives: every genuine use of a name
produces a token that the usage scan counts, so the tool errs toward leaving a
borderline import alone rather than flagging a used one.  Two residual sources
of false positives are inherent to textual analysis and should be verified by a
type-check before removal: names that are only ever resolved by *instance
search*, and names referenced only inside ``{-# … #-}`` pragmas (which are
stripped along with comments).

The report ends with two tables — the files with the most unused names, and the
import names unused in the most files — to show where cleanup pays off most.

Usage
-----

    python3 scripts/python/unused_imports.py                 # scan src/ (skips Legacy)
    python3 scripts/python/unused_imports.py src/Setoid      # scan one subtree
    python3 scripts/python/unused_imports.py --json src      # machine-readable
    python3 scripts/python/unused_imports.py --summary src   # tables + counts only
    python3 scripts/python/unused_imports.py --show-open-ended src
    python3 scripts/python/unused_imports.py --fix src/Setoid  # remove them in place

``--fix`` deletes the unused names (surgically from ``using`` / ``renaming``
lists, or the whole statement when nothing remains), leaving formatting intact;
statements sharing a line with another are left for manual handling.  Because the
analysis is textual, **always re-type-check after ``--fix``** — a name resolved
only by instance search or used only inside a pragma can be a false positive.

Exit status is ``1`` when anything is flagged (so CI can gate on it) and ``0``
otherwise; pass ``--exit-zero`` to always exit ``0``.

Style note
----------

The body is written in the functional idiom the repository favours: pure
functions, immutable ``frozen`` dataclasses, comprehensions, structural
``match``, and recursion for the tree-shaped clause parsing.  The few inherently
sequential scanners — the character lexer (:func:`scan_line`), the bracket
matcher (:func:`take_balanced`), and the logical statement collector
(:func:`collect_statements`) — use explicit loops for O(n) speed and stack
safety; all are pure (no shared state).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass, replace
from functools import reduce
from itertools import accumulate
from pathlib import Path
from typing import Optional

# Import the shared functional utilities the way the sibling scripts do: make
# this file's directory importable, then pull in the Result monad and the pure
# file-reading wrapper.
_SCRIPT_DIR = Path(__file__).resolve().parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))

from _utils import Result, PipelineError  # noqa: E402
from _utils.file_ops import read_text, write_text  # noqa: E402


# =============================================================================
# Immutable data model
# =============================================================================

@dataclass(frozen=True)
class ImportItem:
    """A single name introduced by an import.  ``source`` is the name as it is
    written in the opened module; ``local`` is the name brought into scope (they
    differ under ``renaming``).  ``is_module`` marks ``module X`` entries."""

    source: str
    local: str
    is_module: bool = False


@dataclass(frozen=True)
class Clauses:
    """Accumulated result of parsing the clauses that follow a module path."""

    using_items: tuple[str, ...] = ()      # raw item strings from every using(...)
    rename_items: tuple[str, ...] = ()     # raw "A to B" strings from renaming(...)
    has_using: bool = False                # an explicit using(...) appeared
    hiding: bool = False                   # a hiding(...) appeared
    alias: Optional[str] = None            # the N in "as N"
    public: bool = False
    args: str = ""                         # leftover module-application arguments


EMPTY_CLAUSES = Clauses()


@dataclass(frozen=True)
class ImportStmt:
    """A parsed ``import`` / ``open`` statement."""

    line: int                      # 1-based line of the statement's first physical line
    keyword: str                   # 'open import' | 'import' | 'open'
    module: str                    # module path or local module name
    public: bool
    closed: bool                   # in-scope names are fully enumerable -> analyzable
    in_scope: tuple[ImportItem, ...]
    args: str                      # module-application args (a use site for other names)

    @property
    def is_qualified(self) -> bool:
        """A bare ``import`` (no ``open``): names are reached by qualification."""
        return self.keyword == "import"


@dataclass(frozen=True)
class Finding:
    """One reported problem."""

    path: Path
    line: int
    keyword: str
    module: str
    unused: tuple[str, ...]        # the names (or module path) found unused
    total: int                     # analyzable names in the statement (0 == qualified path)
    category: str                  # 'statement' | 'name' | 'qualified'

    def render(self) -> str:
        loc = f"{self.path}:{self.line}"
        names = ", ".join(self.unused)
        match self.category:
            case "statement":
                return f"{loc}: entire `{self.keyword} {self.module}` unused (none of: {names})"
            case "qualified":
                return f"{loc}: unused qualified `{self.keyword} {self.module}` ({names})"
            case _:
                return f"{loc}: unused in `{self.keyword} {self.module}`: {names}"

    def to_dict(self) -> dict:
        return {
            "path": str(self.path),
            "line": self.line,
            "keyword": self.keyword,
            "module": self.module,
            "unused": list(self.unused),
            "total": self.total,
            "category": self.category,
        }


@dataclass(frozen=True)
class OpenEnded:
    """An import whose in-scope names cannot be enumerated textually."""

    path: Path
    line: int
    keyword: str
    module: str
    reason: str


@dataclass(frozen=True)
class FileReport:
    path: Path
    findings: tuple[Finding, ...]
    open_ended: tuple[OpenEnded, ...]
    analyzed: int                  # number of analyzable statements examined
    public: int                    # number of public statements skipped


# =============================================================================
# Literate extraction:  .lagda.md text -> one Agda line per source line
# =============================================================================

_FENCE_OPEN = re.compile(r"^```\s*(?:agda\b|\{[^}]*\.agda[^}]*\})\s*$")
_FENCE_CLOSE = re.compile(r"^```\s*$")


def _fence_step(inside: bool, line: str) -> bool:
    """State transition for the code-fence scanner: are we inside a code block
    *after* this line?  HTML comments are invisible to Agda, so blocks hidden
    inside ``<!-- … -->`` are treated as code, exactly as Agda type-checks them."""
    if inside:
        return not bool(_FENCE_CLOSE.match(line))
    return bool(_FENCE_OPEN.match(line))


def extract_agda_lines(text: str) -> list[str]:
    """Return one entry per source line: the line's Agda code, or ``''`` for
    prose and fence lines.  Numbering is preserved so diagnostics point at the
    real line in the ``.lagda.md`` file."""
    lines = text.split("\n")
    # inside_before[i] = were we inside a code block before processing line i?
    inside_before = list(accumulate(lines, _fence_step, initial=False))[:-1]
    return [
        line if (inside and not _FENCE_CLOSE.match(line)) else ""
        for inside, line in zip(inside_before, lines)
    ]


# =============================================================================
# Lexer:  blank out comments and string literals, preserving layout
# =============================================================================

# Characters that may continue an operator token after ``--``; if the run of
# dashes is followed by one of these, ``--`` is part of an operator, not a
# comment (e.g. ``-->``).  Otherwise ``--`` starts a line comment.
_SYMBOL_CHARS = frozenset("-!#$%&*+./<=>?@\\^|~:")


def _line_comment_at(line: str, i: int) -> bool:
    """Does a line comment start at position ``i``?  Mirrors Agda's rule: a
    maximal run of ``-`` (length >= 2) followed by a non-symbol char or EOL."""
    if line[i : i + 2] != "--":
        return False
    j = i
    while j < len(line) and line[j] == "-":
        j += 1
    nxt = line[j] if j < len(line) else ""
    return nxt == "" or nxt not in _SYMBOL_CHARS


def scan_line(block_depth: int, line: str) -> tuple[int, str]:
    """Blank comments and string literals in one line, threading the nesting
    depth of ``{- … -}`` block comments across lines.  Replacement preserves
    length so that column positions and later tokenisation are unaffected.

    Note: ASCII ``'`` is a legal identifier character in Agda (primed names such
    as ``cong'``), and character literals do not occur in this corpus, so ``'``
    is left untouched rather than risk eating a name.  Pragmas ``{-# … #-}`` are
    blanked along with ordinary block comments.
    """
    out: list[str] = []
    depth = block_depth
    in_string = False
    i, n = 0, len(line)
    while i < n:
        two = line[i : i + 2]
        c = line[i]
        if depth > 0:                       # inside a block comment / pragma
            if two == "{-":
                depth += 1; out.append("  "); i += 2
            elif two == "-}":
                depth -= 1; out.append("  "); i += 2
            else:
                out.append(" "); i += 1
        elif in_string:                     # inside a "..." literal
            if c == "\\" and i + 1 < n:
                out.append("  "); i += 2
            elif c == '"':
                in_string = False; out.append(" "); i += 1
            else:
                out.append(" "); i += 1
        elif two == "{-":                   # block comment / pragma opens
            depth += 1; out.append("  "); i += 2
        elif _line_comment_at(line, i):     # line comment to EOL
            out.append(" " * (n - i)); break
        elif c == '"':                      # string opens
            in_string = True; out.append(" "); i += 1
        else:
            out.append(c); i += 1
    return depth, "".join(out)


def clean_code_lines(agda_lines: list[str]) -> list[str]:
    """Blank comments/strings across a whole file, line by line."""
    depths = list(accumulate(agda_lines, lambda d, ln: scan_line(d, ln)[0], initial=0))
    return [scan_line(d, ln)[1] for d, ln in zip(depths[:-1], agda_lines)]


def file_code_lines(text: str) -> list[str]:
    """Full front end: ``.lagda.md`` text -> comment-free Agda, line-numbered."""
    return clean_code_lines(extract_agda_lines(text))


# =============================================================================
# Tokenisation and usage detection
# =============================================================================

# Token delimiters: whitespace and the characters Agda always treats as
# separators.  Notably ``_`` , ``,`` and ``[ ]`` are NOT delimiters — they occur
# inside ordinary names (``_,_``, ``[]``, ``if_then_else_``).
_DELIM = re.compile(r"[\s(){};.@\"⦃⦄]+")
# A "word": a module path, alias, or argument token (keeps dots, commas, etc.).
_WORD = re.compile(r"[^\s(){};]+")


def code_tokens(code: str) -> frozenset[str]:
    """The set of name tokens appearing in a blob of code."""
    return frozenset(t for t in _DELIM.split(code) if t)


def name_parts(name: str) -> tuple[str, ...]:
    """The non-empty parts of a (possibly mixfix) name: ``_∙_`` -> ``('∙',)``."""
    return tuple(p for p in name.split("_") if p)


def is_used(name: str, toks: frozenset[str]) -> bool:
    """Is ``name`` used, given the set of tokens from a module's code?  A mixfix
    name is used when its full form or any of its operator parts appears.

    A name of the form ``Foo-syntax`` backs an Agda ``syntax`` declaration whose
    notation opens with ``Foo[`` (e.g. ``Σ-syntax`` is used as ``Σ[ x ∈ A ] B``).
    Such a name never appears verbatim at its use site, so its notation token is
    what we look for instead."""
    if name in toks:
        return True
    if name.endswith("-syntax") and (name[: -len("-syntax")] + "[") in toks:
        return True
    # Operator sections keep one hole glued to the name: `_⊨ˢᵍ_` used as
    # `(_⊨ˢᵍ Th)` tokenises to `_⊨ˢᵍ`, and `(x ∙_)` to `∙_`.
    if {name.lstrip("_"), name.rstrip("_")} & toks:
        return True
    parts = name_parts(name)
    if "_" in name and parts != (name,):
        return any(p in toks for p in parts)
    return False


def dotted_prefixes(path: str) -> frozenset[str]:
    """Every dotted prefix of a module path: ``A.B.C`` -> {A, A.B, A.B.C}.  These
    are the names by which the path can be referenced — as a qualifier (``A.B.x``)
    or by opening it (``open A.B``)."""
    parts = path.split(".")
    return frozenset(".".join(parts[:k]) for k in range(1, len(parts) + 1))


# =============================================================================
# Statement collection:  group physical lines into logical statements
# =============================================================================

_IMPORT_START = re.compile(r"\s*(?:open\s+import|import|open)\b")
_CLAUSE_CONT = re.compile(r"\s*(?:using|renaming|hiding|public|as)\b")


def _is_import_start(line: str) -> bool:
    return bool(_IMPORT_START.match(line))


def _is_clause_cont(line: str) -> bool:
    return bool(_CLAUSE_CONT.match(line))


def _paren_depth(text: str) -> int:
    """Net ``(`` depth (comments already removed, so parentheses balance)."""
    return text.count("(") - text.count(")")


def collect_statements(code_lines: list[str]) -> list[tuple[int, list[int], str]]:
    """Find every ``import`` / ``open`` statement, joining the physical lines a
    statement spans.  A statement continues onto the next line while a clause
    list is still open (unbalanced ``(``) or the next line begins a further
    clause (``using`` / ``renaming`` / …).  Returns, per statement, its 1-based
    start line, the indices of every physical line it occupies, and its text.

    Deliberately an index loop: bounded, O(n), and free of recursion limits.
    """
    out: list[tuple[int, list[int], str]] = []
    n = len(code_lines)
    i = 0
    while i < n:
        if not _is_import_start(code_lines[i]):
            i += 1
            continue
        text = code_lines[i]
        j = i
        while True:
            nxt = code_lines[j + 1] if j + 1 < n else None
            # A statement never continues across a blank line; this also bounds
            # the damage if some upstream edit ever leaves a paren unbalanced.
            if nxt is not None and nxt.strip() != "" and (
                _paren_depth(text) > 0 or _is_clause_cont(nxt)
            ):
                text = text + "\n" + nxt
                j += 1
            else:
                break
        out.append((i + 1, list(range(i, j + 1)), text))
        i = j + 1
    return out


# =============================================================================
# Statement parsing (recursive, structural)
# =============================================================================

def take_balanced(s: str) -> tuple[str, str]:
    """Given ``s`` starting at an opening bracket, return ``(inner, rest)`` where
    ``inner`` is the content up to the matching close and ``rest`` follows it."""
    openers, closers = "([{", ")]}"
    depth = 0
    for idx, c in enumerate(s):
        if c in openers:
            depth += 1
        elif c in closers:
            depth -= 1
            if depth == 0:
                return s[1:idx], s[idx + 1 :]
    return s[1:], ""  # unbalanced (should not happen after comment removal)


def split_semicolons(s: str) -> tuple[str, ...]:
    """Split on ``;`` that sit at bracket depth 0; trim and drop empty pieces."""
    def step(acc: tuple[int, str, tuple[str, ...]], c: str) -> tuple[int, str, tuple[str, ...]]:
        depth, cur, parts = acc
        if c in "([{":
            return depth + 1, cur + c, parts
        if c in ")]}":
            return depth - 1, cur + c, parts
        if c == ";" and depth == 0:
            return depth, "", parts + (cur,)
        return depth, cur + c, parts
    depth, cur, parts = reduce(step, s, (0, "", ()))
    return tuple(p.strip() for p in parts + (cur,) if p.strip())


def parse_clauses(rest: str, acc: Clauses) -> Clauses:
    """Consume ``using`` / ``renaming`` / ``hiding`` / ``as`` / ``public`` clauses
    and module-application arguments from the front of ``rest``, in any order."""
    rest = rest.lstrip()
    if not rest:
        return acc
    kw = _CLAUSE_CONT.match(rest)
    if kw and (word := kw.group(0).strip()) in ("using", "renaming", "hiding"):
        after = rest[kw.end() :].lstrip()
        inner, tail = take_balanced(after) if after.startswith("(") else ("", after)
        items = split_semicolons(inner)
        match word:
            case "using":
                acc = replace(acc, using_items=acc.using_items + items, has_using=True)
            case "renaming":
                acc = replace(acc, rename_items=acc.rename_items + items)
            case "hiding":
                acc = replace(acc, hiding=True)
        return parse_clauses(tail, acc)
    if rest.startswith("as ") or rest == "as":
        after = rest[2:].lstrip()
        m = _WORD.match(after)
        alias = m.group(0) if m else None
        return parse_clauses(after[m.end() :] if m else "", replace(acc, alias=alias))
    if rest.startswith("public"):
        return parse_clauses(rest[len("public") :], replace(acc, public=True))
    if rest[0] in "({":
        inner, tail = take_balanced(rest)
        return parse_clauses(tail, replace(acc, args=acc.args + " " + inner))
    m = _WORD.match(rest)
    return parse_clauses(rest[m.end() :], replace(acc, args=acc.args + " " + m.group(0)))


def parse_using_item(raw: str) -> Optional[ImportItem]:
    """``a`` -> name a; ``module M`` -> module M."""
    parts = raw.split()
    if not parts:
        return None
    if parts[0] == "module":
        return ImportItem(parts[1], parts[1], True) if len(parts) > 1 else None
    return ImportItem(raw.strip(), raw.strip(), False)


_RENAME = re.compile(r"^(module\s+)?(.+?)\s+to\s+(.+)$")


def parse_rename_item(raw: str) -> Optional[ImportItem]:
    """``A to B`` -> item with source A, local B (the new in-scope name)."""
    m = _RENAME.match(raw.strip())
    if not m:
        return None
    return ImportItem(m.group(2).strip(), m.group(3).strip(), bool(m.group(1)))


def parse_statement(line: int, text: str) -> Optional[ImportStmt]:
    """Parse one statement (a single top-level piece, comments already removed)."""
    stripped = text.strip()
    if (m := re.match(r"open\s+import\b", stripped)):
        keyword, opened = "open import", True
    elif (m := re.match(r"import\b", stripped)):
        keyword, opened = "import", False
    elif (m := re.match(r"open\b", stripped)):
        keyword, opened = "open", True
    else:
        return None
    rest = stripped[m.end() :].strip()
    path = _WORD.match(rest)
    if not path:
        return None
    module = path.group(0)
    clauses = parse_clauses(rest[path.end() :], EMPTY_CLAUSES)

    using = tuple(it for x in clauses.using_items if (it := parse_using_item(x)))
    renamed = tuple(it for x in clauses.rename_items if (it := parse_rename_item(x)))
    alias_item = (ImportItem(clauses.alias, clauses.alias, True),) if clauses.alias else ()

    if opened:
        closed = clauses.has_using and not clauses.hiding
        in_scope = using + renamed + alias_item
    else:  # bare `import` (qualified access)
        closed = True
        in_scope = alias_item  # empty -> path-reuse check applies
    return ImportStmt(line, keyword, module, clauses.public, closed, in_scope, clauses.args)


# =============================================================================
# Per-file analysis
# =============================================================================

def evaluate(
    path: Path,
    stmt: ImportStmt,
    toks: frozenset[str],
    usage_text: str,
    module_refs: frozenset[str],
) -> Optional[Finding]:
    """Decide whether ``stmt`` introduces anything unused.  ``toks`` is the set of
    usage tokens; ``usage_text`` is the raw usage corpus (for qualified-path
    substring checks); ``module_refs`` are the module names that *other* statements
    reference — every dotted prefix of their module paths — which is how a module
    or alias brought into scope is used without appearing as a code token (e.g.
    ``open Polymorphic.CommutativeMonoid-Op`` uses the alias ``Polymorphic``, and
    ``open Environment 𝑨`` uses the module ``Environment``)."""
    if stmt.public:
        return None
    if stmt.is_qualified:
        if stmt.in_scope:  # `import M as N` -> check the alias N
            alias = stmt.in_scope[0].local
            if is_used(alias, toks) or alias in module_refs:
                return None
            return Finding(path, stmt.line, stmt.keyword, stmt.module, (alias,), 1, "qualified")
        # `import M` -> used iff the path is re-opened/qualified by another
        # statement or referenced qualified in the code.
        if stmt.module in module_refs or stmt.module in usage_text:
            return None
        return Finding(path, stmt.line, stmt.keyword, stmt.module, (stmt.module,), 0, "qualified")
    if not stmt.closed:
        return None  # whole-module open / hiding / bare renaming: unanalyzable

    # Any imported name may be a module that is used not by a token but by being
    # opened or used as a qualifier in another statement (`open X …`,
    # `open X.Sub …`), whose line is excluded from the token corpus.  This holds
    # whether or not the name was imported with the `module` keyword: a plain
    # `using ( signature )` can still be consumed by a later `open signature`.
    def used(it: ImportItem) -> bool:
        return is_used(it.local, toks) or it.local in module_refs

    unused = tuple(it.local for it in stmt.in_scope if not used(it))
    if not unused:
        return None
    total = len(stmt.in_scope)
    category = "statement" if len(unused) == total else "name"
    return Finding(path, stmt.line, stmt.keyword, stmt.module, unused, total, category)


def open_ended_reason(stmt: ImportStmt) -> Optional[str]:
    """Why a statement is unanalyzable, or ``None`` if it is analyzable."""
    if stmt.public or stmt.is_qualified or stmt.closed:
        return None
    return "whole-module open (no `using`); names cannot be enumerated"


@dataclass(frozen=True)
class Located:
    """A parsed statement together with the original lines it occupies, so the
    ``--fix`` path can edit the exact source span.  ``text`` is the cleaned span
    text; because comment removal preserves length, its character offsets line up
    with the original source.  ``shared`` flags a span that holds more than one
    statement (``open A ; open B``), which the fixer leaves alone."""

    stmt: ImportStmt
    span: tuple[int, ...]   # 0-based original line indices
    text: str               # cleaned joined text of the span
    shared: bool


@dataclass(frozen=True)
class Scan:
    """Everything a single file's analysis produces, shared by report and fix."""

    path: Path
    findings: tuple[tuple[Located, Finding], ...]
    open_ended: tuple[OpenEnded, ...]
    analyzed: int
    public: int


def scan_file(path: Path, text: str) -> Scan:
    """Parse, classify, and evaluate every import/open statement in one file."""
    code_lines = file_code_lines(text)
    raws = collect_statements(code_lines)
    consumed = frozenset(i for _, span, _ in raws for i in span)

    parsed = [
        (s, tuple(span), joined)
        for start, span, joined in raws
        for piece in split_semicolons(joined)
        for s in (parse_statement(start, piece),)
        if s is not None
    ]
    span_counts = Counter(span for _, span, _ in parsed)
    located = tuple(
        Located(s, span, joined, span_counts[span] > 1) for s, span, joined in parsed
    )

    # Usage corpus: all non-import code, plus the argument lists of imports
    # (module applications such as `{𝑆 = 𝑆}` are genuine use sites), but never
    # the import keywords, module paths, or using/renaming/hiding lists.
    non_import = "\n".join(ln for i, ln in enumerate(code_lines) if i not in consumed)
    args = "\n".join(loc.stmt.args for loc in located)
    usage_text = non_import + "\n" + args
    toks = code_tokens(usage_text)

    # The module names each statement can be referenced by; a statement is judged
    # against the references made by all the *others*.
    prefixes = [dotted_prefixes(loc.stmt.module) for loc in located]
    others = [
        frozenset().union(*(prefixes[j] for j in range(len(located)) if j != i))
        if len(located) > 1 else frozenset()
        for i in range(len(located))
    ]
    findings = tuple(
        (loc, f)
        for i, loc in enumerate(located)
        if (f := evaluate(path, loc.stmt, toks, usage_text, others[i]))
    )
    open_ended = tuple(
        OpenEnded(path, loc.stmt.line, loc.stmt.keyword, loc.stmt.module, reason)
        for loc in located
        if (reason := open_ended_reason(loc.stmt))
    )
    analyzed = sum(
        1 for loc in located if not loc.stmt.public and (loc.stmt.closed or loc.stmt.is_qualified)
    )
    public = sum(1 for loc in located if loc.stmt.public)
    return Scan(path, findings, open_ended, analyzed, public)


def analyze_file(path: Path, text: str) -> FileReport:
    """Produce the findings and open-ended report for one file."""
    scan = scan_file(path, text)
    return FileReport(
        path,
        tuple(f for _, f in scan.findings),
        scan.open_ended,
        scan.analyzed,
        scan.public,
    )


# =============================================================================
# Automatic removal (--fix)
# =============================================================================

def clause_regions(text: str) -> list[tuple[int, int]]:
    """Offsets ``(start, end)`` of the content inside each ``using`` / ``renaming``
    / ``hiding`` parenthesised list in a statement (comments already removed)."""
    regions: list[tuple[int, int]] = []
    for m in re.finditer(r"\b(?:using|renaming|hiding)\b", text):
        opener = text.find("(", m.end())
        if opener < 0:
            continue
        depth = 0
        for k in range(opener, len(text)):
            if text[k] in "([{":
                depth += 1
            elif text[k] in ")]}":
                depth -= 1
                if depth == 0:
                    regions.append((opener + 1, k))
                    break
    return regions


def segment_spans(inner: str) -> list[tuple[int, int]]:
    """Offsets of the ``;``-separated items inside a clause body (depth 0)."""
    spans: list[tuple[int, int]] = []
    depth, start = 0, 0
    for i, c in enumerate(inner):
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == ";" and depth == 0:
            spans.append((start, i))
            start = i + 1
    spans.append((start, len(inner)))
    return spans


def item_local_name(item: str) -> Optional[str]:
    """The in-scope name an item introduces (``A to B`` -> B, ``module M`` -> M)."""
    item = item.strip()
    if (rm := _RENAME.match(item)):
        return rm.group(3).strip()
    parsed = parse_using_item(item)
    return parsed.local if parsed else None


def remove_items(cleaned: str, original: str, unused: frozenset[str]) -> str:
    """Rebuild each ``using`` / ``renaming`` clause of a statement, dropping items
    whose in-scope name is in ``unused`` and keeping the survivors' original text
    (so spacing and line breaks are preserved).  Offsets come from ``cleaned`` (the
    comment-free text); the survivor text is sliced from ``original`` at the same
    offsets, which line up because comment removal preserves length.  Clauses are
    disjoint and edited right-to-left, and only a clause's interior is replaced, so
    the parentheses always stay balanced — this is what makes the rewrite safe to
    iterate.  Rebuilding from survivors (rather than deleting per name) also avoids
    the overlapping-separator hazard when several adjacent items are removed."""
    result = original
    for cs, ce in sorted(clause_regions(cleaned), key=lambda r: r[0], reverse=True):
        cleaned_inner = cleaned[cs:ce]
        original_inner = original[cs:ce]
        segs = segment_spans(cleaned_inner)
        survivors = [
            original_inner[s:e]
            for s, e in segs
            if item_local_name(cleaned_inner[s:e]) not in unused
        ]
        if len(survivors) == len(segs):
            continue  # nothing removed from this clause
        result = result[:cs] + ";".join(survivors) + result[ce:]
    return result


@dataclass(frozen=True)
class FixResult:
    path: Path
    removed_names: int
    removed_statements: int
    manual: tuple[str, ...]       # findings the fixer declined to touch
    new_text: Optional[str]        # None when nothing changed


def fix_file(path: Path, text: str) -> FixResult:
    """Compute the edited source for one file by deleting its unused imports.

    Whole-statement and qualified findings delete the statement's line span;
    individual-name findings rebuild each ``using`` / ``renaming`` list from its
    surviving items (see :func:`remove_items`), preserving the rest of the line.
    Statements that share a line with another statement are left for manual
    handling.  The character offsets from the cleaned text apply unchanged to the
    original source because comment removal is length-preserving."""
    scan = scan_file(path, text)
    orig_lines = text.split("\n")
    edits: dict[int, tuple[tuple[int, ...], list[str]]] = {}
    manual: list[str] = []
    removed_names = removed_statements = 0

    for loc, finding in scan.findings:
        where = f"{path}:{finding.line}: `{finding.keyword} {finding.module}`"
        if loc.shared:
            manual.append(f"{where} shares a line with another statement")
            continue
        if finding.category in ("statement", "qualified"):
            edits[min(loc.span)] = (loc.span, [])
            removed_statements += 1
            continue
        orig_joined = "\n".join(orig_lines[i] for i in loc.span)
        new_joined = remove_items(loc.text, orig_joined, frozenset(finding.unused))
        if new_joined == orig_joined:  # e.g. an unused `as N` alias — leave by hand
            manual.append(f"{where}: could not remove {', '.join(finding.unused)} automatically")
            continue
        edits[min(loc.span)] = (loc.span, new_joined.split("\n"))
        removed_names += len(finding.unused)

    if not edits:
        return FixResult(path, 0, 0, tuple(manual), None)

    spanned = {i for span, _ in edits.values() for i in span}
    rebuilt: list[str] = []
    i = 0
    while i < len(orig_lines):
        if i in edits:
            span, new_lines = edits[i]
            rebuilt.extend(new_lines)
            i = max(span) + 1
        elif i in spanned:
            i += 1  # interior line of a span whose start was already emitted
        else:
            rebuilt.append(orig_lines[i])
            i += 1
    return FixResult(path, removed_names, removed_statements, tuple(manual), "\n".join(rebuilt))


# =============================================================================
# Summary tables
# =============================================================================

def _aligned(rows: list[tuple[str, ...]], headers: tuple[str, ...]) -> list[str]:
    """Render rows as a left/right padded text table (numeric columns right-aligned)."""
    cols = list(zip(*([headers] + rows))) if rows else [(h,) for h in headers]
    widths = [max(len(c) for c in col) for col in cols]
    numeric = [all(c.isdigit() for c in col[1:]) for col in cols]
    def fmt(row: tuple[str, ...]) -> str:
        cells = [c.rjust(w) if num else c.ljust(w) for c, w, num in zip(row, widths, numeric)]
        return "  " + "  ".join(cells).rstrip()
    return [fmt(headers)] + [fmt(r) for r in rows]


def summary_tables(reports: list[FileReport], top: int) -> list[str]:
    """Two tables: the files with the most unused names, and the import names that
    are unused in the most files — the places where cleanup pays off most."""
    findings = [f for r in reports for f in r.findings]
    if not findings:
        return []

    scored = [
        (sum(len(f.unused) for f in r.findings),
         sum(1 for f in r.findings if f.category != "name"),
         r.path)
        for r in reports
        if r.findings
    ]
    scored.sort(key=lambda s: (-s[0], str(s[2])))
    file_rows = [(str(n), str(w), str(p)) for n, w, p in scored[:top]]
    file_head = (
        f"Top files by unused imports (showing {len(file_rows)} of {len(scored)}):"
    )

    pair_files: dict[tuple[str, str], set[Path]] = defaultdict(set)
    for r in reports:
        for f in r.findings:
            for name in f.unused:
                pair_files[(f.module, name)].add(r.path)
    pairs = sorted(pair_files.items(), key=lambda kv: (-len(kv[1]), kv[0][0], kv[0][1]))
    pair_rows = [(str(len(files)), f"{mod} → {name}") for (mod, name), files in pairs[:top]]
    pair_head = f"Most-repeated unused imports (showing {len(pair_rows)} of {len(pairs)}):"

    return (
        ["", file_head]
        + _aligned(file_rows, ("unused", "whole", "file"))
        + ["", pair_head]
        + _aligned(pair_rows, ("files", "import"))
    )


# =============================================================================
# Driver
# =============================================================================

def expand_target(p: Path, include_legacy: bool) -> list[Path]:
    """A path argument -> the ``.lagda.md`` files it denotes.  Explicitly named
    files are always honoured; directory walks skip frozen ``Legacy/`` unless
    asked to include it."""
    if p.is_file():
        return [p]
    if p.is_dir():
        return [
            q
            for q in sorted(p.rglob("*.lagda.md"))
            if include_legacy or "/Legacy/" not in q.as_posix()
        ]
    return []


def gather_files(paths: list[Path], include_legacy: bool) -> list[Path]:
    return sorted({f for p in paths for f in expand_target(p, include_legacy)})


def read_and_analyze(path: Path) -> Result[FileReport, PipelineError]:
    """IO boundary: read a file (in the Result monad) and analyze it."""
    return read_text(path).map(lambda text: analyze_file(path, text))


def render_report(
    reports: list[FileReport],
    errors: list[tuple[Path, PipelineError]],
    *,
    summary_only: bool,
    show_open_ended: bool,
    tables: bool,
    top: int,
) -> None:
    findings = [f for r in reports for f in r.findings]
    if not summary_only:
        for f in findings:
            print(f.render())
        if show_open_ended:
            for oe in (oe for r in reports for oe in r.open_ended):
                print(f"{oe.path}:{oe.line}: open-ended `{oe.keyword} {oe.module}` "
                      f"(not analyzed: {oe.reason})")
    for path, err in errors:
        print(f"!! {path}: {err}", file=sys.stderr)

    statements_unused = sum(1 for f in findings if f.category in ("statement", "qualified"))
    names_unused = sum(len(f.unused) for f in findings if f.category == "name")
    analyzed = sum(r.analyzed for r in reports)
    open_ended = sum(len(r.open_ended) for r in reports)
    if tables:
        for line in summary_tables(reports, top):
            print(line)
    print(
        f"\nScanned {len(reports)} files, {analyzed} analyzable statements: "
        f"{len(findings)} flagged "
        f"({statements_unused} whole statements, {names_unused} individual names); "
        f"{open_ended} open-ended statements not analyzed."
    )


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="Flag unused import/open statements in Agda .lagda.md modules."
    )
    parser.add_argument("paths", nargs="*", help="files or directories (default: src)")
    parser.add_argument("--include-legacy", action="store_true",
                        help="also scan src/Legacy (skipped by default)")
    parser.add_argument("--json", action="store_true", help="emit findings as JSON")
    parser.add_argument("--summary", action="store_true", help="print only the summary line")
    parser.add_argument("--show-open-ended", action="store_true",
                        help="also list whole-module opens that cannot be analyzed")
    parser.add_argument("--exit-zero", action="store_true",
                        help="always exit 0 (do not signal findings via exit status)")
    parser.add_argument("--no-tables", action="store_true",
                        help="suppress the summary tables")
    parser.add_argument("--top", type=int, default=20, metavar="N",
                        help="rows to show in each summary table (default: 20)")
    parser.add_argument("--fix", action="store_true",
                        help="remove the unused imports in place (re-type-check afterward!)")
    args = parser.parse_args(argv)

    paths = [Path(p) for p in (args.paths or ["src"])]
    files = gather_files(paths, args.include_legacy)
    if not files:
        print("no .lagda.md files found in: " + ", ".join(map(str, paths)), file=sys.stderr)
        return 2

    if args.fix:
        return run_fix(files)

    results = [(f, read_and_analyze(f)) for f in files]
    reports = [r.unwrap() for _, r in results if r.is_ok]
    errors = [(f, r.unwrap_err()) for f, r in results if r.is_err]
    findings = [f for r in reports for f in r.findings]

    if args.json:
        print(json.dumps([f.to_dict() for f in findings], ensure_ascii=False, indent=2))
    else:
        render_report(reports, errors, summary_only=args.summary,
                      show_open_ended=args.show_open_ended,
                      tables=not args.no_tables, top=args.top)

    return 0 if (args.exit_zero or not findings) else 1


def run_fix(files: list[Path]) -> int:
    """Apply ``--fix``: read each file, delete its unused imports, write it back."""
    changed = total_names = total_statements = 0
    manual: list[str] = []
    for path in files:
        read = read_text(path)
        if read.is_err:
            print(f"!! {path}: {read.unwrap_err()}", file=sys.stderr)
            continue
        result = fix_file(path, read.unwrap())
        manual.extend(result.manual)
        if result.new_text is None:
            continue
        write = write_text(path, result.new_text)
        if write.is_err:
            print(f"!! {path}: {write.unwrap_err()}", file=sys.stderr)
            continue
        changed += 1
        total_names += result.removed_names
        total_statements += result.removed_statements
        print(f"fixed {path}: removed {result.removed_statements} statement(s), "
              f"{result.removed_names} name(s)")

    for note in manual:
        print(f"manual: {note}")
    print(
        f"\nApplied fixes to {changed} files: removed {total_statements} statements "
        f"and {total_names} names; {len(manual)} finding(s) left for manual handling."
    )
    print("IMPORTANT: re-type-check now (e.g. `make check`) — textual analysis can "
          "miss names used only via instance search or inside pragmas.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
