"""
File: scripts/python/_utils/literate.py

Description: Literate-Agda (``.lagda.md``) front end shared by the corpus tools.

  Every module under ``src/`` is literate Markdown (ADR-004): Agda code lives
  inside ```` ```agda ```` fenced blocks and everything outside a fence is
  prose.  What counts as a fence is what Agda's own reader says (see
  :func:`_md_step`), so the tools see the code Agda checks.  Three tools now read that structure: ``unused_imports.py`` (which
  needs the Agda code with comments blanked), ``docstring_audit.py`` (which
  needs the *prose* attached to each fence as well), and ``corpus_stats.py``
  (which counts the code and reads each module's pragma), so the front end
  lives here rather than in any one of them.

  Three layers, each a pure function of the file text:

    1. ``fences``            -> the fenced blocks, with the prose run preceding
                                each one and whether the fence is *hidden*
                                inside an ``<!-- … -->`` HTML comment;
    2. ``extract_agda_lines`` -> one entry per source line, the Agda code or
                                ``''``, so diagnostics keep real line numbers;
    3. ``clean_code_lines``   -> the same, with comments and string literals
                                blanked (length-preserving, so columns survive).

  Then ``options_pragma``, which reads the ``OPTIONS`` a module is checked
  under.  It stands apart from the three because it must see what they erase:
  layer 3 blanks pragmas along with comments, by design.

Design Principles:
  Line numbering is preserved at every layer: a tool reports ``path:line`` into
  the ``.lagda.md`` source, never into a reconstructed code-only buffer.
"""
from __future__ import annotations

import re
from dataclasses import dataclass
from itertools import accumulate
from pathlib import Path
from types import MappingProxyType
from typing import Mapping, Sequence


# =============================================================================
# Fences:  where the Agda code blocks are, and what prose precedes them
# =============================================================================

# Agda's reader of literate Markdown (``literateMd`` in
# ``Agda.Syntax.Parser.Literate``, at the pinned revision) decides what is code,
# so the tools follow it exactly.  Each of its three patterns must match a whole
# line, as follows:
#
#   +  a line that *ends* in ``` or ```agda opens an Agda block, whatever comes
#      before it on the line (`<!-- ```agda` opens one, and so does an indented
#      fence, and so does a bare ```: the Makefile does not pass
#      --literate-markdown-only-agda-blocks);
#   +  any other fence, such as ```text, opens a block that is not Agda and runs
#      to its closer, so an ```agda line shown inside it opens nothing;
#   +  a closer is ``` alone on its line, indented or not.
#
# An attribute form such as ```{.agda .hidden} matches neither opener: Agda reads
# that line as prose, and the ``` that closes it as an opener.
_MD_BEGIN = re.compile(r"(?P<pre>.*?)\s*```(?:agda)?\s*")
_MD_BEGIN_OTHER = re.compile(r"\s*```[a-zA-Z0-9-]*\s*")
_MD_END = re.compile(r"\s*```\s*")

# The reader's three states: prose, an Agda block, a block of something else.
_PROSE, _CODE, _OTHER = "prose", "code", "other"


def _md_step(state: str, line: str) -> str:
    """The reader's state after ``line``, given its state before it."""
    if state != _PROSE:
        return _PROSE if _MD_END.fullmatch(line) else state
    if _MD_BEGIN.fullmatch(line):
        return _CODE
    return _OTHER if _MD_BEGIN_OTHER.fullmatch(line) else _PROSE

# HTML comment delimiters.  The corpus writes them on their own lines around a
# hidden preamble fence, but single-line `<!-- … -->` also occurs in prose.
_COMMENT_OPEN = "<!--"
_COMMENT_CLOSE = "-->"


@dataclass(frozen=True)
class Fence:
    """One ```` ```agda ```` block, with the prose that introduces it.

    ``open_line`` / ``close_line`` are 1-based line numbers of the fence
    delimiters themselves; ``body`` is the code between them.  ``prose`` is the
    run of lines between the previous fence (or the YAML front matter) and this
    fence's opener, reduced to what actually renders — text inside HTML
    comments is dropped (see :func:`visible_prose`).
    """

    open_line: int
    close_line: int
    hidden: bool
    body: tuple[str, ...]
    prose: tuple[str, ...]

    @property
    def body_start(self) -> int:
        """1-based line number of the fence's first body line."""
        return self.open_line + 1


def visible_prose(line: str, inside: bool) -> tuple[str, bool]:
    """The part of a prose line that *renders*, and the comment state after it.

    Text inside ``<!-- … -->`` is dropped, not merely unwrapped.  Keeping it
    would let an HTML comment count as documentation, and the corpus prescribes
    ``<!-- TODO(#268): … -->`` as the marker for prose that could *not* yet be
    written — exactly the thing that must not satisfy a coverage check.  Text
    sharing the line outside the comment is kept, so a paragraph followed by an
    ``<!-- aside -->`` still counts.

    HTML comments do not nest, so a boolean carries the state across lines.
    """
    out: list[str] = []
    index = 0
    while index < len(line):
        if inside:
            close = line.find(_COMMENT_CLOSE, index)
            if close < 0:
                return "".join(out), True
            index, inside = close + len(_COMMENT_CLOSE), False
        else:
            open_at = line.find(_COMMENT_OPEN, index)
            if open_at < 0:
                out.append(line[index:])
                return "".join(out), False
            out.append(line[index:open_at])
            index, inside = open_at + len(_COMMENT_OPEN), True
    return "".join(out), inside


def front_matter_end(lines: Sequence[str]) -> int:
    """How many leading lines a YAML front-matter block (``---`` … ``---``)
    occupies, delimiters included: ``0`` when there is none.

    A block opens only on the file's first line and needs a closing ``---``;
    without one there is no block, and nothing is metadata.
    """
    if not lines or lines[0].strip() != "---":
        return 0
    return next((index + 1 for index, line in enumerate(lines[1:], 1)
                 if line.strip() == "---"), 0)


def strip_front_matter(lines: tuple[str, ...]) -> tuple[str, ...]:
    """Drop a leading YAML front-matter block (``---`` … ``---``).

    Every module opens with Jekyll/MkDocs front matter (STYLE_GUIDE § "Jekyll/
    MkDocs YAML frontmatter").  It is metadata, never prose, so it must not
    count as the documentation preceding the first code fence.

    Apply this only to a run of lines that starts at the top of the file.  A
    ``---`` elsewhere is a horizontal rule, and there are 23 of them in the live
    trees; treating one as an opening delimiter would silently swallow the prose
    up to the next rule.
    """
    return lines[front_matter_end(lines):]


# A front-matter entry: a key, a colon, a value.  YAML allows space before the
# colon, and 149 modules write `title :` and `date :` that way, so this must too.
_FRONT_MATTER_ENTRY = re.compile(r"([A-Za-z][\w-]*)\s*:\s*(.*?)\s*")


def _unquote(value: str) -> str:
    """A YAML scalar without its surrounding quotes, if it has a matching pair."""
    if len(value) >= 2 and value[0] == value[-1] and value[0] in "\"'":
        return value[1:-1]
    return value


def front_matter(text: str) -> Mapping[str, str]:
    """The ``key: value`` entries of a module's front matter, values unquoted.

    The corpus writes flat entries only (``layout``, ``file``, ``title``,
    ``date``, ``author``, and ``check-cost`` on a slow module), so this reads
    those and nothing else: a line that is not a flat entry is skipped rather
    than guessed at, and a repeated key keeps its last value, as YAML loaders
    do.  A file with no block (see :func:`front_matter_end`) has no entries.
    """
    lines = text.split("\n")
    end = front_matter_end(lines)
    entries = (match.groups() for line in lines[1:max(end - 1, 1)]
               if (match := _FRONT_MATTER_ENTRY.fullmatch(line)))
    return MappingProxyType({key: _unquote(value) for key, value in entries})


def fences(text: str) -> tuple[Fence, ...]:
    """Every ```` ```agda ```` block in a literate file, in source order.

    A fence is ``hidden`` when its opener sits inside an HTML comment: the
    corpus wraps each module's pragma/header/imports preamble in ``<!-- … -->``
    so it type-checks but does not render.  Agda sees hidden and visible fences
    alike; a reader sees only the visible ones.
    """
    lines = text.split("\n")
    out: list[Fence] = []
    in_comment = False
    state = _PROSE
    open_line = 0
    hidden = False
    pending: list[str] = []
    for index, line in enumerate(lines):
        if state == _CODE:
            if _MD_END.fullmatch(line):
                out.append(Fence(
                    open_line=open_line + 1,
                    close_line=index + 1,
                    hidden=hidden,
                    body=tuple(lines[open_line + 1:index]),
                    # Only the file's opening run can hold front matter; a
                    # later `---` is a horizontal rule (see strip_front_matter).
                    prose=(strip_front_matter(tuple(pending)) if not out
                           else tuple(pending)),
                ))
                state, pending = _PROSE, []
            continue
        opener = _MD_BEGIN.fullmatch(line) if state == _PROSE else None
        if opener:
            # Text before the fence on its line is prose, and may open the
            # HTML comment that hides the fence (`<!-- ```agda`).
            rendered, in_comment = visible_prose(opener.group("pre"), in_comment)
            if rendered.strip():
                pending.append(rendered)
            state, open_line, hidden = _CODE, index, in_comment
            continue
        # Prose, or a block of something else, which renders as text.
        state = _md_step(state, line)
        rendered, in_comment = visible_prose(line, in_comment)
        pending.append(rendered)
    return tuple(out)


# =============================================================================
# Literate extraction:  .lagda.md text -> one Agda line per source line
# =============================================================================

def extract_agda_lines(text: str) -> list[str]:
    """Return one entry per source line: the line's Agda code, or ``''`` for
    prose and fence lines.  Numbering is preserved so diagnostics point at the
    real line in the ``.lagda.md`` file.  HTML comments are invisible to Agda,
    so blocks hidden inside ``<!-- … -->`` are code, exactly as Agda checks
    them."""
    lines = text.split("\n")
    # before[i] = the reader's state before line i.
    before = list(accumulate(lines, _md_step, initial=_PROSE))[:-1]
    return [
        line if (state == _CODE and not _MD_END.fullmatch(line)) else ""
        for state, line in zip(before, lines)
    ]


# =============================================================================
# Lexer:  blank out comments and string literals, preserving layout
# =============================================================================

# Characters after which a new token begins, besides whitespace.
_TOKEN_ENDS = frozenset('(){};@"')


def _line_comment_at(line: str, i: int) -> bool:
    """Does a line comment start at position ``i``?  Agda's lexer reads ``--``
    as the start of a comment wherever a token begins (at the start of a line,
    after whitespace, or after a delimiter), whatever follows the dashes: its
    rule for a comment, ``"--" .*``, is longer than any operator it could
    begin, so ``-->`` and ``--|`` open comments.  Inside a name, as in
    ``_--_``, the dashes are part of the name."""
    if line[i : i + 2] != "--":
        return False
    return i == 0 or line[i - 1].isspace() or line[i - 1] in _TOKEN_ENDS


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
# The OPTIONS pragma a module is actually checked under
# =============================================================================

_OPTIONS_PRAGMA = re.compile(r"\{-#\s*OPTIONS\b([^#]*)#-\}")


def options_pragma(code: str) -> str | None:
    """The options Agda applies to a module, or ``None`` if it declares none.

    Agda requires ``{-# OPTIONS … #-}`` to precede the module header, so only
    whitespace and comments may come before it.  This walks the code that way:
    a line comment (Agda's ``--`` rule, as :func:`_line_comment_at` states it)
    and a block comment (``{- … -}``, which nests, and which ``{-#`` does *not*
    open) are skipped, another pragma is skipped, the first ``OPTIONS`` pragma
    reached is the answer, and anything else is real code, which means the
    module carries no pragma.

    Neither simpler reading works.  :func:`clean_code_lines` blanks pragmas
    along with comments, by design, so a search over cleaned code finds no
    pragma at all; a search over raw code accepts a pragma that is *commented
    out*, and would call a module ``--safe`` on the strength of a line its
    author had disabled.
    """
    i, n, depth = 0, len(code), 0
    while i < n:
        if code[i].isspace():
            i += 1
        elif depth:                              # inside {- … -}: everything is text
            if code.startswith("{-", i):
                depth, i = depth + 1, i + 2
            elif code.startswith("-}", i):
                depth, i = depth - 1, i + 2
            else:
                i += 1
        elif code.startswith("{-#", i):          # a pragma, not a comment
            end = code.find("#-}", i)
            if end < 0:
                return None                      # unterminated; Agda applies nothing
            match = _OPTIONS_PRAGMA.fullmatch(code[i:end + 3])
            if match:
                return match.group(1)
            i = end + 3                          # some other pragma; keep looking
        elif code.startswith("{-", i):
            depth, i = 1, i + 2
        elif _line_comment_at(code, i):
            newline = code.find("\n", i)
            i = n if newline < 0 else newline
        else:
            return None                          # real code before any OPTIONS
    return None


# =============================================================================
# File discovery
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
    """The sorted, de-duplicated set of files denoted by several path arguments."""
    return sorted({f for p in paths for f in expand_target(p, include_legacy)})
