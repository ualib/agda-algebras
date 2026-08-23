#!/usr/bin/env python3
"""
File: scripts/python/docstring_audit.py

Description: Audit (and harvest) the prose block attached to every public
  definition in the literate Agda corpus.

  ``docs/STYLE_GUIDE.md`` § "Every public definition has a prose comment block"
  requires that a public definition carry "a prose comment block immediately
  above it", and that in a ``.lagda.md`` module that prose be "Markdown
  preceding the code fence (not ``-- |`` comments inside it)".  Issue #268 asks
  for a "grep-based audit" enforcing this.  A grep cannot do it: the library
  holds essentially no ``-- |`` comments, so a comment-grep reports the whole
  corpus as undocumented, while a prose-grep cannot tell which definition a
  paragraph belongs to.  The check has to understand literate structure —
  prose outside the fences, definitions inside them — and Agda's layout rule,
  because almost every definition in this corpus is *indented* inside an
  anonymous ``module _ … where``, not at column 0.

  The same traversal answers the inverse question.  "Which public definitions
  have no preceding prose?" and "what is the prose preceding each public
  definition?" are one walk over the corpus, so this module exposes both: an
  ``audit`` report (issue #268) and a ``--json`` harvest whose records join to
  the Agda-internal corpus of issue #275 on ``qname``.  An Agda-internal
  extractor sees types and terms but cannot see Markdown; the prose is what
  this repository uniquely holds.

Design Principles:
  Pure core, effectful shell.  ``analyze_text`` is a total function from file
  text to a tuple of ``Definition`` records; every classification decision is a
  pure function of the parse.  Reading files, printing, and exit codes happen
  only in ``main`` and its immediate helpers.

  The parser errs toward *under*-reporting a definition rather than
  misattributing prose: a construct it cannot classify is counted in the
  ``unparsed`` tally and named in the report, so a blind spot is visible rather
  than silently absorbed into a clean score.

Usage::

    python3 scripts/python/docstring_audit.py                  # audit src/
    python3 scripts/python/docstring_audit.py src/Setoid       # one subtree
    python3 scripts/python/docstring_audit.py --list           # name every gap
    python3 scripts/python/docstring_audit.py --strict         # fail on `grouped` too
    python3 scripts/python/docstring_audit.py --json src       # harvest for #275
    python3 scripts/python/docstring_audit.py --modules        # per-module prose audit
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import time
from collections import Counter
from itertools import groupby
from dataclasses import dataclass, replace
from enum import Enum
from pathlib import Path
from typing import Iterable, Optional

# Import the shared functional utilities the way the sibling scripts do: make
# this file's directory importable, then pull in the Result monad, the pure
# file-reading wrapper, and the literate front end.
_SCRIPT_DIR = Path(__file__).resolve().parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))

from _utils import PipelineError  # noqa: E402
from _utils.file_ops import read_text  # noqa: E402
from _utils.literate import Fence, clean_code_lines, fences, gather_files  # noqa: E402
from _utils.agda_names import (  # noqa: E402
    NO_NOTATIONS,
    SyntaxNotations,
    code_tokens,
    harvest_syntax_notations,
    is_used,
    name_parts,
)


# =============================================================================
# Immutable data model
# =============================================================================

class Kind(Enum):
    """What sort of declaration a definition is."""

    SIGNATURE = "signature"    # `name : type` — function, value, or type family
    RECORD = "record"          # `record Name … where`
    DATA = "data"              # `data Name … where`
    MODULE = "module"          # a *named* submodule (a public namespace)
    PATTERN = "pattern"        # `pattern Name … = …`


class Prose(Enum):
    """What the prose run preceding a fence amounts to."""

    PARAGRAPH = "paragraph"      # at least one real paragraph of prose
    BOILERPLATE = "boilerplate"  # only "This is the [X][] module of the [AUA Library][]"
    HEADING = "heading"          # only heading lines (and blanks)
    NONE = "none"                # nothing at all


class Status(Enum):
    """A definition's documentation status.

    ``DOCUMENTED`` is the style guide's bar met exactly: the definition opens a
    fence and a real paragraph sits immediately above that fence.  ``GROUPED``
    is the common near-miss — a documented fence holding several definitions,
    where the block plausibly covers them all but does not sit "immediately
    above" each.  The remaining three are unambiguous gaps.
    """

    DOCUMENTED = "documented"
    GROUPED = "grouped"
    HEADING_ONLY = "heading-only"
    BOILERPLATE = "boilerplate"
    UNDOCUMENTED = "undocumented"


#: Statuses that fail the acceptance criterion under the default (lenient)
#: reading: the definition's fence carries no real prose at all.
GAP_STATUSES = frozenset({Status.HEADING_ONLY, Status.BOILERPLATE, Status.UNDOCUMENTED})

#: Additionally failing under ``--strict``: the style guide's literal
#: "immediately above" wording, which a shared block does not satisfy.
STRICT_GAP_STATUSES = GAP_STATUSES | {Status.GROUPED}


@dataclass(frozen=True)
class Definition:
    """One public definition and the prose block that introduces it."""

    module: str          # dotted module name, from the path under src/
    path: str            # repo-relative path of the .lagda.md file
    line: int            # 1-based line of the declaration head
    name: str            # the declared name, as written (may be mixfix)
    namespace: tuple[str, ...]   # enclosing *named* submodules, outermost first
    kind: Kind
    status: Status
    prose_kind: Prose
    fence_index: int         # 0-based index of the fence among the file's fences
    position_in_fence: int   # 1-based rank among the public definitions in it
    signature: str           # the declaration text, whitespace-normalized
    prose: str               # the preceding prose block, verbatim

    @property
    def named(self) -> bool:
        """Is this definition *mentioned by name* in the prose above its fence?

        The weaker sibling of ``status``.  A fence can carry a real paragraph
        that never mentions half the definitions under it, which is the common
        way documentation drifts away from the code it sits above.  Prose that
        genuinely describes a definition almost always names it, so this is a
        cheap drift detector — not a quality measure, since it is satisfied by
        merely listing names.
        """
        if not self.prose:
            return False
        if self.name in self.prose:
            return True
        # A mixfix name is written applied in prose: `_∘_` appears as `∘`.
        parts = name_parts(self.name)
        return bool(parts) and all(p in self.prose for p in parts)

    @property
    def qname(self) -> str:
        """The fully qualified name — the join key with the Agda-internal
        corpus of issue #275."""
        return ".".join((self.module, *self.namespace, self.name))


@dataclass(frozen=True)
class FileReport:
    """Everything the audit learned about one module."""

    path: str
    module: str
    definitions: tuple[Definition, ...]
    module_prose: Prose      # the prose introducing the module's first fence
    hidden_defs: tuple[Definition, ...]   # declarations inside hidden fences
    unparsed: tuple[tuple[int, str], ...]  # (line, text) the parser declined


# =============================================================================
# Agda layout: the scope stack
# =============================================================================

class Block(Enum):
    """A layout block, classified by what it does to the publicness of the
    declarations inside it."""

    MODULE = "module"            # named or anonymous — public scope continues
    RECORD = "record"            # body holds members and fields, not free defs
    DATA = "data"                # body holds constructors
    PRIVATE = "private"          # everything inside is module-private
    LOCAL = "local"              # a definition's `where` body, or `let`
    FIELD = "field"              # record field block
    POSTULATE = "postulate"      # items are signatures, and are public
    VARIABLE = "variable"        # generalized variables, not definitions
    TRANSPARENT = "transparent"  # mutual / abstract / instance / macro


#: Keywords that open a layout block all by themselves.
_BLOCK_KEYWORDS: dict[str, Block] = {
    "private": Block.PRIVATE,
    "field": Block.FIELD,
    "postulate": Block.POSTULATE,
    "variable": Block.VARIABLE,
    "mutual": Block.TRANSPARENT,
    "abstract": Block.TRANSPARENT,
    "instance": Block.TRANSPARENT,
    "macro": Block.TRANSPARENT,
}

#: Blocks that make the declarations inside them non-public, or not standalone
#: definitions at all.  ``RECORD``/``DATA``/``FIELD`` members are public API,
#: but they are documented by their record's or datatype's own prose block —
#: Markdown cannot be interleaved between a record's fields.
_OPAQUE = frozenset({
    Block.PRIVATE, Block.LOCAL, Block.FIELD, Block.VARIABLE,
    Block.RECORD, Block.DATA,
})

#: Line-initial keywords that are declarations of something other than a
#: definition, and so are never reported.
_NON_DEFINITION_HEADS = frozenset({
    "open", "import", "infix", "infixl", "infixr", "syntax",
    "constructor", "eta-equality", "no-eta-equality", "inductive",
    "coinductive", "overlap", "using", "renaming", "hiding", "public",
    "unquoteDecl", "unquoteDef", "primitive",
})


@dataclass(frozen=True)
class Frame:
    """An open layout block.  ``indent`` is the column its items start at, or
    ``-1`` while the block is *pending* — opened by a keyword or a ``where``
    whose first item has not been seen yet, so its column is not yet known.
    ``opener`` is the column of the item that opened the block, which is what
    decides whether the block turns out to have any items at all."""

    kind: Block
    indent: int
    opener: int
    name: Optional[str] = None   # for Block.MODULE: the submodule's name, if named


def _indent_of(line: str) -> int:
    """Column of the first non-space character (the line must be non-blank)."""
    return len(line) - len(line.lstrip())


def _resolve_pending(stack: tuple[Frame, ...], indent: int) -> tuple[Frame, ...]:
    """Settle every block that is still waiting for its first item.

    A pending block owns the next line only if that line is indented deeper
    than the item that opened it.  Otherwise the block is empty and is
    discarded — the case that matters is a definition whose ``where`` body was
    written inline (``f x = e where open M``), which opens a block that the
    following sibling definition must not be swallowed into.
    """
    while stack and stack[-1].indent < 0:
        if indent > stack[-1].opener:
            return (*stack[:-1], replace(stack[-1], indent=indent))
        stack = stack[:-1]
    return stack


def _close_to(stack: tuple[Frame, ...], indent: int) -> tuple[Frame, ...]:
    """Pop every block whose items are indented deeper than this line: layout
    closes a block as soon as a line appears to the left of its items."""
    while stack and 0 <= stack[-1].indent > indent:
        stack = stack[:-1]
    return stack


def _settle(stack: tuple[Frame, ...], indent: int) -> tuple[Frame, ...]:
    """Bring the scope stack to the state a line at ``indent`` sees.

    Resolution runs on both sides of the close: before, so a block claims the
    line that is its first item; after, so a block whose inner blocks just
    closed — and which this line turns out not to belong to — is discarded
    rather than left open over the rest of the file.
    """
    return _resolve_pending(_close_to(_resolve_pending(stack, indent), indent), indent)


def _is_public(stack: tuple[Frame, ...]) -> bool:
    """A declaration is a *standalone public definition* when no enclosing block
    hides it (``private``, a ``where`` body, a ``let``) and none makes it a
    member of something else (a record body, a field block, a variable block)."""
    return not any(f.kind in _OPAQUE for f in stack)


def _namespace(stack: tuple[Frame, ...]) -> tuple[str, ...]:
    """The chain of enclosing *named* submodules.  Anonymous ``module _`` frames
    contribute nothing: their contents are exported into the parent scope."""
    return tuple(f.name for f in stack if f.kind is Block.MODULE and f.name)


# =============================================================================
# Declaration recognition
# =============================================================================

# `where` as a standalone token, and everything before it.
_WHERE = re.compile(r"(?<![\w'-])where(?![\w'-])")
# A line that *ends* by opening a layout block, so its indented body consists of
# items in its own right rather than continuation lines of the opener.  `where`
# is handled separately because it may carry its block's first item inline.
_ENDS_OPENER = re.compile(
    r"(?<![\w'-])(?:private|field|postulate|variable|mutual|abstract|instance|macro)\s*$")
# A type signature: one or more names, then a colon delimited by whitespace.
# Agda requires the space before `:` (a bare `:` may be part of a mixfix name),
# which makes this a reliable split point.
_SIGNATURE = re.compile(r"^(?P<names>\S+(?:\s+\S+)*?)\s+:\s")
# `record R …`, `data D …`, `module M …`, `pattern p …`
_HEADED = re.compile(r"^(record|data|module|pattern)(?![\w'-])\s*(?P<rest>.*)$")
# A name token: anything not a delimiter.  Mixfix names (`_∘_`, `∣_∣`, `⨅`) are
# ordinary tokens; parentheses and braces are not part of a name.
_NAME_OK = re.compile(r"^[^\s(){}@;.]+$")


def _split_where(text: str) -> tuple[str, Optional[str]]:
    """Split a declaration at its ``where``: the head, and the block's inline
    first item if the source put one on the same line (``… where foo = bar``).
    Returns ``(head, None)`` when there is no ``where``."""
    match = _WHERE.search(text)
    if not match:
        return text, None
    tail = text[match.end():].strip()
    return text[:match.start()].rstrip(), (tail if tail else "")


def _declared_names(head: str) -> tuple[str, ...]:
    """The names a type signature declares.  Agda allows ``f g : T`` to declare
    two names at once, so this returns a tuple.  Returns ``()`` when the text is
    not a signature the tool is willing to claim."""
    match = _SIGNATURE.match(head)
    if not match:
        return ()
    names = tuple(match.group("names").split())
    return names if all(_NAME_OK.match(n) for n in names) else ()


def _headed_name(rest: str) -> Optional[str]:
    """The name introduced by ``record`` / ``data`` / ``module`` / ``pattern``.
    ``None`` for the anonymous ``module _``, which names no namespace."""
    first = rest.split()[0] if rest.split() else ""
    return None if first in ("_", "") else first


# =============================================================================
# The parse
# =============================================================================

def _opens_block(line: str) -> bool:
    """Does this line end the declaration it belongs to by opening a block?

    Either it contains a ``where``, or it ends with a standalone layout keyword.
    The second case matters as much as the first: a bare ``postulate`` line
    followed by two indented signatures would otherwise fold all three into one
    logical item, and only the first signature would be recognised — silently,
    with nothing in the ``unparsed`` tally to show for it.
    """
    return bool(_WHERE.search(line) or _ENDS_OPENER.search(line))


@dataclass(frozen=True)
class _Item:
    """One logical declaration: the physical line it starts on, the column it
    starts at, and its text with continuation lines folded in."""

    line: int
    indent: int
    text: str


def _logical_items(lines: Iterable[tuple[int, str]]) -> list[_Item]:
    """Fold Agda's continuation lines into logical items.

    A line indented deeper than the item in progress continues it — *unless*
    the item has already reached its ``where``, which opens a nested block whose
    contents are items in their own right.  Everything else is decided by the
    scope stack in :func:`_walk`; this pass only has to stop swallowing lines at
    the right moment, so it tracks the in-progress item's own column and
    whether a ``where`` has closed it off.

    Only the *newly added* line is searched for ``where``, never the accumulated
    item.  The two are equivalent — parts are stripped and joined with a space,
    so no token can straddle the boundary, and the negative lookbehind is
    satisfied by both a space and a start-of-string — but searching the
    accumulation is quadratic in the item's length, which the FLRP certificate
    modules punish severely: a single list literal there runs to thousands of
    lines and is one logical item.  Measured over ``src/``, the accumulating
    form cost 38 s of a 41 s run.
    """
    items: list[_Item] = []
    start, indent, parts, done = 0, -1, [], True
    for lineno, line in lines:
        if not line.strip():
            continue
        col = _indent_of(line)
        if not done and col > indent:
            parts.append(line.strip())
            if _opens_block(line):
                items.append(_Item(start, indent, " ".join(parts)))
                done = True
            continue
        if not done:
            items.append(_Item(start, indent, " ".join(parts)))
        start, indent, parts, done = lineno, col, [line.strip()], False
        if _opens_block(line):
            items.append(_Item(start, indent, " ".join(parts)))
            done = True
    if not done:
        items.append(_Item(start, indent, " ".join(parts)))
    return items


@dataclass(frozen=True)
class _Decl:
    """A recognized declaration, before prose is attached."""

    line: int
    names: tuple[str, ...]
    kind: Kind
    namespace: tuple[str, ...]
    text: str


def _walk(
    items: list[_Item], seen: frozenset[str], stack: tuple[Frame, ...] = ()
) -> tuple[list[_Decl], list[tuple[int, str]], frozenset[str], tuple[Frame, ...]]:
    """Walk the logical items under Agda's layout rule, collecting the
    standalone public declarations and the items the parser declined.

    Two pieces of state are threaded in and out, because a fence boundary is a
    Markdown event and not an Agda one — a scope opened in one code block
    routinely continues in the next.

    ``seen`` carries the names already declared in this module, which is what
    distinguishes a *clause* from a declaration: ``f x with e``, ``f x ()``, and
    ``f (suc n) = …`` all begin with a name that has a signature above them.

    ``stack`` carries the open layout blocks.  Without it a ``module Sub where``
    left open at the end of a fence is forgotten, so the definitions continuing
    beneath it in the next fence lose their namespace — the wrong ``qname``, and
    ``qname`` is the join key for the corpus of #275 — and a ``private`` block
    split the same way would present its declarations as public.  Both occur:
    75 fences in the live trees end with a named module or a ``private`` block
    still open.
    """
    decls: list[_Decl] = []
    unparsed: list[tuple[int, str]] = []
    for item in items:
        stack, found, skipped = _classify(_settle(stack, item.indent), item, seen)
        decls.extend(found)
        unparsed.extend(skipped)
        seen = seen | {n for d in found for n in d.names}
    return decls, unparsed, seen, stack


def _classify(
    stack: tuple[Frame, ...], item: _Item, seen: frozenset[str] = frozenset()
) -> tuple[tuple[Frame, ...], list[_Decl], list[tuple[int, str]]]:
    """Classify one logical item, returning the updated scope stack, any public
    declarations it introduces, and any text the parser declined to judge."""
    text = item.text.strip()
    if not text:
        return stack, [], []
    first = text.split()[0]

    # A block keyword (`private`, `field`, `postulate`, …) opens a block.  When
    # the source puts the block's first item on the same line (`private
    # variable`), recurse into the remainder at its own column.
    if first in _BLOCK_KEYWORDS:
        stack = (*stack, Frame(_BLOCK_KEYWORDS[first], -1, item.indent))
        rest = text[len(first):].strip()
        if rest:
            # `private variable`, `private postulate`: the inner block opens too,
            # and both blocks take the *outer* column as their opener, because
            # that is the column their items will be measured against.
            return _classify(stack, replace(item, text=rest), seen)
        return stack, [], []

    head, inline = _split_where(text)
    public = _is_public(stack)
    namespace = _namespace(stack)

    headed = _HEADED.match(head)
    if headed:
        keyword, rest = headed.group(1), headed.group("rest")
        name = _headed_name(rest)
        kind = {"record": Kind.RECORD, "data": Kind.DATA,
                "module": Kind.MODULE, "pattern": Kind.PATTERN}[keyword]
        block = {"record": Block.RECORD, "data": Block.DATA,
                 "module": Block.MODULE}.get(keyword)
        # `module M where` and `pattern p = …` differ: only the former opens a
        # block.  A `record`/`data` with no `where` is a forward declaration.
        if block is not None and inline is not None:
            stack = (*stack, Frame(block, -1, item.indent,
                                   name if block is Block.MODULE else None))
        # An anonymous `module _` introduces a scope, not a definition.  A named
        # submodule is itself public API; `module M = N …` is an application,
        # which names a namespace but declares nothing new to document.
        emit = public and name is not None and not (
            kind is Kind.MODULE and "=" in rest.split("where")[0]
        )
        found = [_Decl(item.line, (name,), kind, namespace, head)] if emit else []
        return stack, found, []

    if first in _NON_DEFINITION_HEADS:
        return stack, [], []

    names = _declared_names(head)
    if names:
        # A signature inside a `postulate` block is still a public definition;
        # one inside a record body, a field block, or `private` is not.
        found = [_Decl(item.line, names, Kind.SIGNATURE, namespace, head)] if public else []
        # `f x = e where …` — the `where` body is local to the definition.
        if inline is not None:
            stack = (*stack, Frame(Block.LOCAL, -1, item.indent))
        return stack, found, []

    # An equation (`f x = e`), a clause of an already-declared name (`f x with
    # e`, an absurd `f x ()`), a clause continuation (`... | p`), or something
    # the parser does not recognize.  Equations and clauses are not reported —
    # the style guide requires an explicit type signature on every public
    # definition, so the signature is the declaration.  Anything else at a
    # public item position is a genuine blind spot and is surfaced as one.
    if inline is not None:
        stack = (*stack, Frame(Block.LOCAL, -1, item.indent))
    is_clause = "=" in head or first in seen or first.startswith("...")
    if public and not is_clause and not head.startswith("_"):
        return stack, [], [(item.line, text[:120])]
    return stack, [], []


# =============================================================================
# Usage: is a definition referenced anywhere in the corpus?
# =============================================================================

@dataclass(frozen=True)
class UsageIndex:
    """Which modules reference which names, corpus-wide.

    "Used" means the name occurs at a *use site* — inside a term or a type —
    rather than only in an ``import``/``open`` statement, which is why import
    statements are dropped before tokenising.  A definition counts as used when
    some other module references it, or when its own module does so outside the
    definition's own signature and clauses; self-recursion alone is therefore
    not use.

    The analysis is textual and its one real inaccuracy is name collision: two
    modules declaring the same short name cannot be told apart, so a use of
    either makes both look used.  ``ambiguous`` records precisely those names,
    so the figure can be reported with its own error bar rather than quietly
    overstated.
    """

    #: token -> the modules whose non-import code contains it
    modules_by_token: dict[str, frozenset[str]]
    #: module -> token -> the heads of the items in which it occurs
    heads_by_token: dict[str, dict[str, frozenset[str]]]
    #: module -> every non-import token (the fallback path)
    by_module: dict[str, frozenset[str]]
    #: names declared in more than one module
    ambiguous: frozenset[str]
    notations: SyntaxNotations

    def _used_elsewhere(self, name: str, home: str) -> bool:
        """Referenced by some module other than the one that declares it.

        ``is_used`` is a disjunction over a handful of candidate spellings for
        every name except a ``syntax``-backed one, where it is a conjunction over
        the notation's literals.  The disjunctive case is answered from the
        inverted index in a few lookups; the handful of ``-syntax`` names fall
        back to scanning modules, which is affordable because there are seven of
        them in the corpus.
        """
        if name.endswith("-syntax"):
            return any(module != home and is_used(name, tokens, self.notations)
                       for module, tokens in self.by_module.items())
        candidates = {name, name.lstrip("_"), name.rstrip("_")}
        if "_" in name:
            candidates |= set(name_parts(name))
        return any(self.modules_by_token.get(c, frozenset()) - {home}
                   for c in candidates if c)

    def _used_at_home(self, name: str, home: str) -> bool:
        """Referenced within its own module, by something other than itself.

        The token set is rebuilt excluding the items the name owns — its
        signature and its clauses — rather than subtracting that name's tokens
        from the module's, which would also delete tokens that other items
        happen to share, and would delete the name itself, making a local use
        undetectable.
        """
        heads = self.heads_by_token.get(home, {})
        local = frozenset(token for token, owners in heads.items() if owners - {name})
        return is_used(name, local, self.notations)

    def used(self, definition: Definition) -> bool:
        """Is this definition referenced outside its own declaration?"""
        return (self._used_elsewhere(definition.name, definition.module)
                or self._used_at_home(definition.name, definition.module))


_IMPORT_LINE = re.compile(r"^\s*(?:open\s+import|import|open)\b")
_CLAUSE_LINE = re.compile(r"^\s*(?:using|renaming|hiding|public|as)\b")


def _item_tokens(items: list[_Item]) -> list[tuple[str, frozenset[str]]]:
    """``(head token, tokens)`` for each item that is not an import statement."""
    out: list[tuple[str, frozenset[str]]] = []
    for item in items:
        if _IMPORT_LINE.match(item.text) or _CLAUSE_LINE.match(item.text):
            continue
        words = item.text.split()
        if words:
            out.append((words[0], code_tokens(item.text)))
    return out


def build_usage_index(
    texts: list[tuple[Path, str]], reports: list[FileReport]
) -> UsageIndex:
    """Index the whole corpus once, so each definition's usage is a lookup.

    A corpus-wide pass is unavoidable: a name declared in one module is normally
    used in another, and a ``syntax`` declaration anywhere changes what a use
    site looks like everywhere.  ``reports`` is threaded in rather than
    recomputed, since the caller has already analyzed every module.
    """
    notations = harvest_syntax_notations(texts)
    modules_by_token: dict[str, set[str]] = {}
    heads_by_token: dict[str, dict[str, frozenset[str]]] = {}
    by_module: dict[str, frozenset[str]] = {}
    for path, text in texts:
        mod = module_name(path)
        pairs = _item_tokens([it for fence in fences(text)
                              for it in _logical_items(_fence_lines(fence))])
        per_token: dict[str, frozenset[str]] = {}
        for head, tokens in pairs:
            for token in tokens:
                per_token[token] = per_token.get(token, frozenset()) | {head}
                modules_by_token.setdefault(token, set()).add(mod)
        heads_by_token[mod] = per_token
        by_module[mod] = frozenset(per_token)
    declared = Counter(d.name for r in reports for d in r.definitions)
    return UsageIndex(
        modules_by_token={k: frozenset(v) for k, v in modules_by_token.items()},
        heads_by_token=heads_by_token, by_module=by_module,
        ambiguous=frozenset(n for n, c in declared.items() if c > 1),
        notations=notations)


# =============================================================================
# Prose classification
# =============================================================================

# The boilerplate header sentence the M4 audit's finding 3 flags: a module whose
# entire prose body is "This is the [X][] module of the [AUA Library][]".
_BOILERPLATE = re.compile(
    r"^\s*This is the .{0,120}? module of the \[Agda Universal Algebra Library\]",
    re.IGNORECASE,
)
_HEADING = re.compile(r"^\s{0,3}#{1,6}\s")
# Structure, not prose: a kramdown/pandoc attribute line, a horizontal rule, or
# an HTML tag alone on its line …
_NON_PROSE = re.compile(r"^\s*(\{[:#][^}]*\}|-{3,}|\*{3,}|<[^>]+>)\s*$")
# … and a link-reference definition, whose target runs to end of line.  These
# are how the corpus defines its cross-links (ADR-007); they render as nothing.
_LINK_DEF = re.compile(r"^ {0,3}\[[^\]]+\]:\s+\S")


def classify_prose(lines: Iterable[str]) -> Prose:
    """What a run of Markdown lines amounts to as documentation."""
    body = [ln for ln in lines if ln.strip()]
    if not body:
        return Prose.NONE
    paragraphs = [ln for ln in body
                  if not _HEADING.match(ln) and not _NON_PROSE.match(ln)
                  and not _LINK_DEF.match(ln)]
    if not paragraphs:
        return Prose.HEADING
    if all(_BOILERPLATE.match(ln) for ln in paragraphs):
        return Prose.BOILERPLATE
    return Prose.PARAGRAPH


def status_for(prose_kind: Prose, position: int) -> Status:
    """A definition's status, from the prose on its fence and its rank in it."""
    if prose_kind is Prose.NONE:
        return Status.UNDOCUMENTED
    if prose_kind is Prose.HEADING:
        return Status.HEADING_ONLY
    if prose_kind is Prose.BOILERPLATE:
        return Status.BOILERPLATE
    return Status.DOCUMENTED if position == 1 else Status.GROUPED


# =============================================================================
# Per-file analysis
# =============================================================================

def module_name(path: Path) -> str:
    """The dotted Agda module name a path under ``src/`` denotes."""
    parts = path.as_posix().split("src/", 1)[-1]
    return parts[: -len(".lagda.md")].replace("/", ".")


def rendered_prose(blocks: tuple[Fence, ...]) -> dict[int, tuple[str, ...]]:
    """The prose a *reader* sees above each visible fence.

    A hidden ``<!-- … -->`` preamble fence renders as nothing, so prose written
    above it sits, on the rendered page, immediately above the next visible code
    block.  Attribution therefore accumulates prose across hidden fences: each
    visible fence gets every prose line since the previous *visible* fence.
    Without this, the corpus idiom — module header, hidden preamble, first
    definitions — would report every module's opening definitions as having no
    prose at all, which is not what the page shows.
    """
    out: dict[int, tuple[str, ...]] = {}
    pending: tuple[str, ...] = ()
    for index, fence in enumerate(blocks):
        pending = pending + fence.prose
        if not fence.hidden:
            out[index] = pending
            pending = ()
    return out


def _fence_lines(fence: Fence) -> list[tuple[int, str]]:
    """A fence's body as ``(1-based file line, cleaned Agda text)`` pairs, with
    comments and string literals blanked."""
    cleaned = clean_code_lines(list(fence.body))
    return [(fence.body_start + i, line) for i, line in enumerate(cleaned)]


def analyze_text(path: Path, text: str) -> FileReport:
    """The whole audit for one literate module, as a pure function of its text."""
    mod = module_name(path)
    blocks = fences(text)
    prose_of = rendered_prose(blocks)
    visible: list[Definition] = []
    hidden: list[Definition] = []
    unparsed: list[tuple[int, str]] = []
    # The module's own header prose is whatever precedes its first fence,
    # hidden or not — that is the block STYLE_GUIDE § "Module headers have
    # comment blocks" asks for.
    module_prose = classify_prose(blocks[0].prose) if blocks else Prose.NONE
    seen: frozenset[str] = frozenset()
    stack: tuple[Frame, ...] = ()
    for index, fence in enumerate(blocks):
        decls, skipped, seen, stack = _walk(
            _logical_items(_fence_lines(fence)), seen, stack)
        prose = prose_of.get(index, ())
        kind = classify_prose(prose)
        # Every name a declaration introduces gets its own record, but they
        # share a rank: `f g : T` is one prose-block-worth of definition.
        rank = 0
        for decl in decls:
            # The file's own `module M where` header declares no new name.  It
            # is written either fully qualified or as the final segment alone.
            if decl.kind is Kind.MODULE and not decl.namespace \
                    and decl.names[0] in (mod, mod.rsplit(".", 1)[-1]):
                continue
            rank += 1
            for name in decl.names:
                record = Definition(
                    module=mod, path=path.as_posix(), line=decl.line, name=name,
                    namespace=decl.namespace, kind=decl.kind,
                    status=status_for(kind, rank), prose_kind=kind,
                    fence_index=index, position_in_fence=rank,
                    signature=decl.text, prose="\n".join(prose).strip(),
                )
                (hidden if fence.hidden else visible).append(record)
        if not fence.hidden:
            unparsed.extend(skipped)
    return FileReport(
        path=path.as_posix(), module=mod, definitions=tuple(visible),
        module_prose=module_prose, hidden_defs=tuple(hidden),
        unparsed=tuple(unparsed),
    )


# =============================================================================
# Reporting
# =============================================================================

def subtree_of(path: str) -> str:
    """The top-level subtree a module belongs to (``Setoid``, ``Classical``, …);
    top-level umbrella modules are grouped under ``(top level)``."""
    rest = path.split("src/", 1)[-1]
    return rest.split("/")[0] if "/" in rest else "(top level)"


@dataclass(frozen=True)
class Tally:
    """Definition counts for one subtree, by status, plus the two softer
    measures: how many definitions their own prose names, and how many are
    referenced anywhere in the corpus."""

    subtree: str
    counts: Counter
    named: int = 0
    used: int = 0

    @property
    def total(self) -> int:
        return sum(self.counts.values())

    @property
    def documented(self) -> int:
        return self.counts[Status.DOCUMENTED]

    @property
    def gaps(self) -> int:
        return sum(self.counts[s] for s in GAP_STATUSES)


def tally(reports: Iterable[FileReport],
          usage: Optional[UsageIndex] = None) -> list[Tally]:
    """Per-subtree status counts, ordered by how much work each subtree needs."""
    by_subtree: dict[str, Counter] = {}
    named: Counter = Counter()
    used: Counter = Counter()
    for report in reports:
        key = subtree_of(report.path)
        bucket = by_subtree.setdefault(key, Counter())
        for definition in report.definitions:
            bucket[definition.status] += 1
            named[key] += definition.named
            if usage is not None:
                used[key] += usage.used(definition)
    return sorted((Tally(name, counts, named[name], used[name])
                   for name, counts in by_subtree.items()),
                  key=lambda t: (-t.gaps, -t.total, t.subtree))


def _row(cells: tuple[str, ...], widths: tuple[int, ...]) -> str:
    return "  ".join(c.rjust(w) if i else c.ljust(w)
                     for i, (c, w) in enumerate(zip(cells, widths)))


def _pct(part: int, whole: int) -> str:
    return f"{100 * part // whole}%" if whole else "-"


def render_table(tallies: list[Tally], with_usage: bool) -> list[str]:
    """The per-subtree summary table: the answer to "how big is #268?".

    The last two columns are softer than the rest and are read differently.

    ``named`` is the share of definitions that the prose above their own fence
    mentions by name.  It is a drift indicator, not a gate: a fence can carry a
    fine paragraph that never mentions half the definitions beneath it.

    ``used`` is the share referenced somewhere in the live trees, and it is the
    guide to where documentation effort pays off — a heavily-used definition is
    one many readers will meet.  It is *not* a dead-code measure.  In a proof
    library an unreferenced definition is usually a terminal result: a theorem
    that is the point in itself (the ``roundtrip-*`` faithfulness lemmas of
    ``Classical/Bundles/`` are the clearest case), an example, or an entry point
    used only by consumers outside this repository.
    """
    headers = ("subtree", "defs", "documented", "grouped", "heading", "boiler",
               "none", "gaps", "named", "used")

    def cells(t: Tally) -> tuple[str, ...]:
        return (t.subtree, str(t.total), str(t.documented),
                str(t.counts[Status.GROUPED]), str(t.counts[Status.HEADING_ONLY]),
                str(t.counts[Status.BOILERPLATE]), str(t.counts[Status.UNDOCUMENTED]),
                str(t.gaps), _pct(t.named, t.total),
                _pct(t.used, t.total) if with_usage else "-")

    rows = [cells(t) for t in tallies]
    total = Tally("TOTAL", sum((t.counts for t in tallies), Counter()),
                  sum(t.named for t in tallies), sum(t.used for t in tallies))
    rows.append(cells(total))
    widths = tuple(max(len(r[i]) for r in (headers, *rows)) for i in range(len(headers)))
    sep = "  ".join("-" * w for w in widths)
    return [_row(headers, widths), sep,
            *(_row(r, widths) for r in rows[:-1]), sep, _row(rows[-1], widths)]


def render_unused(reports: list[FileReport], usage: UsageIndex) -> list[str]:
    """Definitions nothing in the live trees references.

    Read as a prompt, not a verdict: most are terminal results or examples, some
    are entry points for consumers outside this repository, and a few are dead.
    """
    dead = [d for r in reports for d in r.definitions if not usage.used(d)]
    lines = [f"\n{len(dead)} definition(s) not referenced anywhere in the live trees:"]
    for d in sorted(dead, key=lambda d: (d.path, d.line)):
        flag = "  [name is ambiguous]" if d.name in usage.ambiguous else ""
        lines.append(f"  {d.path}:{d.line}  {d.kind.value:9s} {d.name}{flag}")
    return lines


def render_modules(reports: list[FileReport]) -> list[str]:
    """Modules whose own header prose is missing or boilerplate — the M4 audit's
    finding 3, enumerated rather than estimated."""
    weak = [r for r in reports if r.module_prose in (Prose.BOILERPLATE, Prose.NONE, Prose.HEADING)]
    lines = [f"{len(weak)} of {len(reports)} modules have no real header prose:"]
    for report in sorted(weak, key=lambda r: (r.module_prose.value, r.path)):
        lines.append(f"  [{report.module_prose.value:11s}] {report.path}")
    return lines


def render_gaps(reports: list[FileReport], statuses: frozenset[Status]) -> list[str]:
    """Every public definition whose status is in ``statuses``, grouped by file."""
    lines: list[str] = []
    for report in reports:
        gaps = [d for d in report.definitions if d.status in statuses]
        if not gaps:
            continue
        lines.append(f"\n{report.path}  ({len(gaps)} undocumented)")
        lines.extend(f"  {d.line:5d}  [{d.status.value:12s}] {d.kind.value:9s} {d.name}"
                     for d in gaps)
    return lines


def to_record(definition: Definition, usage: Optional[UsageIndex] = None,
              hidden: bool = False) -> dict:
    """A harvest record: the prose this repository holds, keyed so it joins to
    the Agda-internal (type, term) corpus of issue #275 on ``qname``."""
    return {
        "qname": definition.qname,
        "module": definition.module,
        "name": definition.name,
        "namespace": list(definition.namespace),
        "file": definition.path,
        "line": definition.line,
        "kind": definition.kind.value,
        "signature": definition.signature,
        "prose": definition.prose,
        "prose_kind": definition.prose_kind.value,
        "status": definition.status.value,
        "named_in_prose": definition.named,
        "hidden": hidden,
        **({} if usage is None else {"used": usage.used(definition),
                                     "name_is_ambiguous": definition.name in usage.ambiguous}),
    }


# =============================================================================
# Driver
# =============================================================================

@dataclass(frozen=True)
class Progress:
    """Where the run narrates itself.

    Effectful edge: nothing below :func:`main` constructs or calls one.  Lines go
    to *stderr* so that ``--json`` keeps stdout clean and pipeable, and each
    carries the elapsed time so a slow subtree is visible as it happens rather
    than inferred afterwards.
    """

    quiet: bool
    started: float

    def note(self, message: str) -> None:
        if not self.quiet:
            sys.stderr.write(f"[{time.monotonic() - self.started:6.2f}s] {message}\n")
            sys.stderr.flush()


def analyze_subtrees(
    texts: list[tuple[Path, str]], progress: Progress
) -> list[FileReport]:
    """Analyze every module, narrating one line per subtree as it completes.

    Grouping the work by subtree is what makes the narration useful: 307 modules
    at roughly three seconds is too fast for per-file lines to be readable, and a
    single line at the end says nothing while the run is happening.
    """
    ordered = sorted(texts, key=lambda pair: (subtree_of(pair[0].as_posix()),
                                              pair[0].as_posix()))
    reports: list[FileReport] = []
    for subtree, group in groupby(ordered, key=lambda pair: subtree_of(pair[0].as_posix())):
        batch = [analyze_text(path, text) for path, text in group]
        reports.extend(batch)
        defs = sum(len(r.definitions) for r in batch)
        gaps = sum(1 for r in batch for d in r.definitions if d.status in GAP_STATUSES)
        progress.note(f"  {subtree:<12} {len(batch):>4} modules  {defs:>5} definitions  "
                      f"{gaps:>4} without prose")
    return reports


def read_all(files: list[Path]) -> tuple[list[tuple[Path, str]], list[tuple[Path, PipelineError]]]:
    """IO boundary: read every file in the Result monad, splitting successes
    from failures so a bad read is reported rather than raised."""
    reads = [(f, read_text(f)) for f in files]
    return ([(f, r.unwrap()) for f, r in reads if r.is_ok],
            [(f, r.unwrap_err()) for f, r in reads if r.is_err])


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Audit the prose block attached to every public definition "
                    "in the literate Agda corpus (issue #268).")
    parser.add_argument("paths", nargs="*", default=["src"],
                        help="files or directories (default: src)")
    parser.add_argument("--include-legacy", action="store_true",
                        help="also scan src/Legacy (frozen; skipped by default)")
    parser.add_argument("--list", action="store_true",
                        help="name every undocumented definition, not just the counts")
    parser.add_argument("--modules", action="store_true",
                        help="list modules whose own header prose is missing or boilerplate")
    parser.add_argument("--strict", action="store_true",
                        help="also count `grouped` definitions as gaps (the style "
                             "guide's literal 'immediately above' reading)")
    parser.add_argument("--json", action="store_true",
                        help="emit one harvest record per definition (issue #275)")
    parser.add_argument("--max-gaps", type=int, default=None, metavar="N",
                        help="fail only when the gap count exceeds N.  This is the "
                             "ratchet CI pins to today's count, so the backlog can "
                             "only shrink while #268 is worked through per subtree")
    parser.add_argument("--max-weak-headers", type=int, default=None, metavar="N",
                        help="fail when more than N modules open with no prose "
                             "beyond the boilerplate sentence.  The second half of "
                             "the bar ADR-010 states, ratcheted the same way")
    parser.add_argument("--exit-zero", action="store_true",
                        help="always exit 0 (do not signal gaps via exit status)")
    parser.add_argument("--no-usage", action="store_true",
                        help="skip the corpus-wide usage analysis (the `used` "
                             "column); it needs a second pass over every file")
    parser.add_argument("--unused", action="store_true",
                        help="list the definitions nothing in the live trees "
                             "references (terminal results and examples, mostly)")
    parser.add_argument("--quiet", "-q", action="store_true",
                        help="suppress the progress log on stderr")
    return parser


def main(argv: list[str]) -> int:
    args = build_parser().parse_args(argv)
    progress = Progress(quiet=args.quiet, started=time.monotonic())

    targets = ", ".join(args.paths)
    progress.note(f"scanning {targets}"
                  f"{'' if args.include_legacy else ' (excluding the frozen Legacy tree)'}")
    files = gather_files([Path(p) for p in args.paths], args.include_legacy)
    if not files:
        sys.stderr.write("error: no .lagda.md files found\n")
        return 2
    progress.note(f"discovered {len(files)} literate module(s)")

    texts, failures = read_all(files)
    for path, error in failures:
        sys.stderr.write(f"error: {path}: {error}\n")
    # A file that could not be read contributes no definitions and so no gaps.
    # Left unreported in the exit status, that silently lowers the count the
    # ratchet is comparing against, which is the one thing a coverage gate must
    # never do.
    blocked = tuple(f"{path} could not be read: {error}" for path, error in failures)
    progress.note(f"read {len(texts)} file(s), "
                  f"{sum(len(text) for _, text in texts) // 1024} KiB")

    reports = analyze_subtrees(texts, progress)
    progress.note(f"analyzed {len(reports)} module(s), "
                  f"{sum(len(r.definitions) for r in reports)} public definition(s)")

    usage: Optional[UsageIndex] = None
    if not args.no_usage:
        usage = build_usage_index(texts, reports)
        progress.note(f"indexed usage across {len(usage.by_module)} module(s); "
                      f"{len(usage.ambiguous)} name(s) declared in more than one "
                      f"module and so not attributable")
    # Computed before the report branches, because a measurement failure
    # invalidates the harvest exactly as much as it invalidates the audit: a
    # `docstrings-json` run that silently omits an unreadable module or an
    # unclassified declaration would publish an incomplete corpus and exit 0.
    unparsed = [(r.path, line, text) for r in reports for line, text in r.unparsed]
    blocked += tuple(f"{path}:{line}: unclassified declaration: {text}"
                     for path, line, text in unparsed)
    weak_headers = sum(1 for r in reports if r.module_prose is not Prose.PARAGRAPH)
    progress.note("report follows on stdout" if args.json else "writing report")

    if args.json:
        for report in reports:
            # Hidden-fence declarations are excluded from the audit's counts but
            # not from the harvest: Agda exports them, so a corpus consumer wants
            # them, flagged.  Merged by source line so a module reads in order.
            records = ([(d.line, d, False) for d in report.definitions]
                       + [(d.line, d, True) for d in report.hidden_defs])
            for _, definition, hidden in sorted(records, key=lambda r: r[0]):
                print(json.dumps(to_record(definition, usage, hidden),
                                 ensure_ascii=False))
        # A harvest is not a coverage gate, so documentation gaps do not fail it;
        # measurement failures do.
        return _exit_code(args, gaps=0, weak_headers=0, blocked=blocked)

    statuses = STRICT_GAP_STATUSES if args.strict else GAP_STATUSES
    print("\n".join(render_table(tally(reports, usage), usage is not None)))
    if args.unused and usage is not None:
        print("\n".join(render_unused(reports, usage)))
    if args.modules:
        print()
        print("\n".join(render_modules(reports)))
    if args.list:
        print("\n".join(render_gaps(reports, statuses)))

    hidden = sum(len(r.hidden_defs) for r in reports)
    total = sum(len(r.definitions) for r in reports)
    gaps = sum(1 for r in reports for d in r.definitions if d.status in statuses)
    print(f"\nScanned {len(reports)} modules, {total} public definitions: "
          f"{gaps} without a prose block "
          f"({'strict' if args.strict else 'lenient'} reading).")
    if hidden:
        print(f"{hidden} declaration(s) inside hidden preamble fences "
              f"(not counted; run with --json to see them).")
    if unparsed:
        print(f"{len(unparsed)} item(s) the parser declined to classify:")
        for path, line, text in unparsed[:20]:
            print(f"  {path}:{line}: {text}")
        if len(unparsed) > 20:
            print(f"  … and {len(unparsed) - 20} more")
    return _exit_code(args, gaps, weak_headers, blocked)


def _ratchet(label: str, count: int, ceiling: Optional[int], knob: str) -> int:
    """Compare one measure against its ceiling; 1 when it has risen above it.

    Prints the nudge when the count comes in under, because a ceiling nobody
    lowers stops being a ratchet and becomes a floor.
    """
    if ceiling is None:
        return 0
    if count > ceiling:
        sys.stderr.write(
            f"\n✗ {count} {label} exceeds the agreed ceiling of {ceiling}.\n"
            f"  Document them, or lower {knob} in the Makefile if you have "
            f"cleared some.\n")
        return 1
    if count < ceiling:
        print(f"✓ {count} {label}, under the ceiling of {ceiling}; lower {knob} "
              f"in the Makefile to {count} to lock the gain in.")
    return 0


def _exit_code(args: argparse.Namespace, gaps: int, weak_headers: int,
               blocked: tuple[str, ...] = ()) -> int:
    """Turn the audit into an exit status.

    Three independent reasons to fail.  ``blocked`` holds conditions that make
    the measurement itself untrustworthy — a file that could not be read, an item
    the parser could not classify — and these fail regardless of any ceiling,
    because a ratchet compared against a corrupted count is worse than no
    ratchet.  The other two are the halves of the bar ADR-010 states: definitions
    without a prose block, and modules without a real header.  Both are
    ratcheted, and ``--exit-zero`` opts out of everything.
    """
    if args.exit_zero:
        return 0
    if blocked:
        sys.stderr.write(
            f"\n✗ the audit could not measure {len(blocked)} item(s), so its "
            f"counts are not trustworthy:\n")
        for reason in blocked[:20]:
            sys.stderr.write(f"  {reason}\n")
        if len(blocked) > 20:
            sys.stderr.write(f"  … and {len(blocked) - 20} more\n")
        return 1
    ratcheted = args.max_gaps is not None or args.max_weak_headers is not None
    if ratcheted:
        return max(
            _ratchet("definitions without a prose block", gaps,
                     args.max_gaps, "DOCSTRING_MAX_GAPS"),
            _ratchet("modules without a real header", weak_headers,
                     args.max_weak_headers, "DOCSTRING_MAX_WEAK_HEADERS"))
    return 0 if not gaps and not weak_headers else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
