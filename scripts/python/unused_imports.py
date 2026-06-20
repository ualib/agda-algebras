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

Usage
-----

    python3 scripts/python/unused_imports.py                 # scan src/ (skips Legacy)
    python3 scripts/python/unused_imports.py src/Setoid      # scan one subtree
    python3 scripts/python/unused_imports.py --json src      # machine-readable
    python3 scripts/python/unused_imports.py --summary src   # counts only
    python3 scripts/python/unused_imports.py --show-open-ended src

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

from _utils import Result, PipelineError, ErrorType  # noqa: E402
from _utils.file_ops import read_text  # noqa: E402


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
    parts = name_parts(name)
    if "_" in name and parts != (name,):
        return any(p in toks for p in parts)
    return False


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
            if nxt is not None and (_paren_depth(text) > 0 or _is_clause_cont(nxt)):
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
    opened_modules: frozenset[str],
) -> Optional[Finding]:
    """Decide whether ``stmt`` introduces anything unused.  ``toks`` is the set of
    usage tokens; ``usage_text`` is the raw usage corpus (for qualified-path
    substring checks); ``opened_modules`` are the module names re-opened by an
    ``open M`` statement (the way a qualified ``import M`` is typically used)."""
    if stmt.public:
        return None
    if stmt.is_qualified:
        if stmt.in_scope:  # `import M as N` -> check the alias N
            alias = stmt.in_scope[0].local
            if is_used(alias, toks) or alias in opened_modules:
                return None
            return Finding(path, stmt.line, stmt.keyword, stmt.module, (alias,), 1, "qualified")
        # `import M` -> used iff the path is re-opened or referenced qualified.
        if stmt.module in opened_modules or stmt.module in usage_text:
            return None
        return Finding(path, stmt.line, stmt.keyword, stmt.module, (stmt.module,), 0, "qualified")
    if not stmt.closed:
        return None  # whole-module open / hiding / bare renaming: unanalyzable

    # A name imported as `module X` (or an `as X` alias) may be used not by a
    # token but by being re-opened later (`open X …`); that `open` is itself an
    # import statement, so the use does not appear in the token corpus.
    def used(it: ImportItem) -> bool:
        return is_used(it.local, toks) or (it.is_module and it.local in opened_modules)

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


def analyze_file(path: Path, text: str) -> FileReport:
    """Produce the findings and open-ended report for one file."""
    code_lines = file_code_lines(text)
    raws = collect_statements(code_lines)
    consumed = frozenset(i for _, span, _ in raws for i in span)

    statements = tuple(
        s
        for start, _span, joined in raws
        for piece in split_semicolons(joined)
        for s in (parse_statement(start, piece),)
        if s is not None
    )

    # Usage corpus: all non-import code, plus the argument lists of imports
    # (module applications such as `{𝑆 = 𝑆}` are genuine use sites), but never
    # the import keywords, module paths, or using/renaming/hiding lists.
    non_import = "\n".join(ln for i, ln in enumerate(code_lines) if i not in consumed)
    args = "\n".join(s.args for s in statements)
    usage_text = non_import + "\n" + args
    toks = code_tokens(usage_text)
    opened_modules = frozenset(s.module for s in statements if s.keyword == "open")

    findings = tuple(
        f for s in statements if (f := evaluate(path, s, toks, usage_text, opened_modules))
    )
    open_ended = tuple(
        OpenEnded(path, s.line, s.keyword, s.module, reason)
        for s in statements
        if (reason := open_ended_reason(s))
    )
    analyzed = sum(1 for s in statements if not s.public and (s.closed or s.is_qualified))
    public = sum(1 for s in statements if s.public)
    return FileReport(path, findings, open_ended, analyzed, public)


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
    args = parser.parse_args(argv)

    paths = [Path(p) for p in (args.paths or ["src"])]
    files = gather_files(paths, args.include_legacy)
    if not files:
        print("no .lagda.md files found in: " + ", ".join(map(str, paths)), file=sys.stderr)
        return 2

    results = [(f, read_and_analyze(f)) for f in files]
    reports = [r.unwrap() for _, r in results if r.is_ok]
    errors = [(f, r.unwrap_err()) for f, r in results if r.is_err]
    findings = [f for r in reports for f in r.findings]

    if args.json:
        print(json.dumps([f.to_dict() for f in findings], ensure_ascii=False, indent=2))
    else:
        render_report(reports, errors, summary_only=args.summary,
                      show_open_ended=args.show_open_ended)

    return 0 if (args.exit_zero or not findings) else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
