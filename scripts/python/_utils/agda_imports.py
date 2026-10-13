"""
File: scripts/python/_utils/agda_imports.py

Description: The ``import`` / ``open`` statements of an Agda module, parsed.

  Two tools need the same reading of a module's import statements:
  ``unused_imports.py``, which asks which of the names a statement brings into
  scope are never used, and ``barrels.py``, which follows the ``import`` edges
  between the library's modules to see what a barrel transitively loads.  The
  parser was written for the first and moved here, unchanged, when the second
  needed it.

  It works on the comment-free code lines of :func:`_utils.literate.file_code_lines`:
  :func:`collect_statements` joins the physical lines a statement spans,
  :func:`split_semicolons` separates statements sharing a line, and
  :func:`parse_statement` takes each one apart into an :class:`ImportStmt`.

Design Principles:
  Pure functions over immutable ``frozen`` dataclasses.  The sequential
  scanners (:func:`take_balanced` and :func:`collect_statements`) use explicit
  loops for O(n) speed and stack safety, and share no state.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, replace
from functools import reduce
from typing import Optional


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


# =============================================================================
# Statement collection:  group physical lines into logical statements
# =============================================================================

# A "word": a module path, alias, or argument token (keeps dots, commas, etc.).
# Used only for taking import statements apart, hence not in _utils.agda_names.
_WORD = re.compile(r"[^\s(){};]+")

# Where a keyword ends.  Agda names may contain `-` and `'`, so `\b` is not
# enough: `open-ended` and `as-set` are names, not `open` and `as`.  A keyword
# ends where a name could not continue (whitespace, a delimiter, the end).
_END = r"(?![^\s(){};])"

_IMPORT_START = re.compile(r"\s*(?:open\s+import|import|open)" + _END)
_CLAUSE_CONT = re.compile(r"\s*(?:using|renaming|hiding|public|as)" + _END)
_PUBLIC = re.compile(r"public" + _END)


def _is_import_start(line: str) -> bool:
    return bool(_IMPORT_START.match(line))


def _is_clause_cont(line: str) -> bool:
    return bool(_CLAUSE_CONT.match(line))


def _paren_depth(text: str) -> int:
    """Net ``(`` depth (comments already removed, so parentheses balance)."""
    return text.count("(") - text.count(")")


def _indent(line: str) -> int:
    """The column of a line's first non-blank character."""
    return len(line) - len(line.lstrip())


def _continues(text: str, column: int, gap: bool, nxt: str) -> bool:
    """Does ``nxt`` continue the statement ``text``, which begins at ``column``?

    By Agda's layout rule a line indented past the statement's first column
    does, even across blank lines (module arguments wrapped onto the next line,
    ``{𝑆 = 𝑆} public``, are the common case).  Without a blank line between,
    so does a line inside a clause list still open (unbalanced ``(``) or one
    that begins a further clause (``using`` / ``renaming`` / …).  A blank line
    ends those two, which bounds the damage if an upstream edit ever leaves a
    parenthesis unbalanced.
    """
    if _indent(nxt) > column:
        return True
    return not gap and (_paren_depth(text) > 0 or _is_clause_cont(nxt))


def collect_statements(code_lines: list[str]) -> list[tuple[int, list[int], str]]:
    """Find every ``import`` / ``open`` statement, joining the physical lines a
    statement spans (see :func:`_continues`).  Returns, per statement, its
    1-based start line, the indices of every physical line it occupies, and its
    text.

    Deliberately an index loop: bounded, O(n), and free of recursion limits.
    """
    out: list[tuple[int, list[int], str]] = []
    n = len(code_lines)
    i = 0
    while i < n:
        if not _is_import_start(code_lines[i]):
            i += 1
            continue
        text, column, j = code_lines[i], _indent(code_lines[i]), i
        while True:
            k = j + 1
            while k < n and code_lines[k].strip() == "":
                k += 1
            if k < n and _continues(text, column, k > j + 1, code_lines[k]):
                text = text + "\n" + "\n".join(code_lines[j + 1 : k + 1])
                j = k
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
    if _PUBLIC.match(rest):
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
    if (m := re.match(r"open\s+import" + _END, stripped)):
        keyword, opened = "open import", True
    elif (m := re.match(r"import" + _END, stripped)):
        keyword, opened = "import", False
    elif (m := re.match(r"open" + _END, stripped)):
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
