"""
File: scripts/python/_utils/literate.py

Description: Literate-Agda (``.lagda.md``) front end shared by the corpus tools.

  Every module under ``src/`` is literate Markdown (ADR-004): Agda code lives
  inside ```` ```agda ```` fenced blocks and everything outside a fence is
  prose.  Two tools now need to read that structure — ``unused_imports.py``
  (which needs the Agda code with comments blanked) and ``docstring_audit.py``
  (which needs the *prose* attached to each fence as well) — so the front end
  lives here rather than in either of them.

  Three layers, each a pure function of the file text:

    1. ``fences``            -> the fenced blocks, with the prose run preceding
                                each one and whether the fence is *hidden*
                                inside an ``<!-- … -->`` HTML comment;
    2. ``extract_agda_lines`` -> one entry per source line, the Agda code or
                                ``''``, so diagnostics keep real line numbers;
    3. ``clean_code_lines``   -> the same, with comments and string literals
                                blanked (length-preserving, so columns survive).

Design Principles:
  Line numbering is preserved at every layer: a tool reports ``path:line`` into
  the ``.lagda.md`` source, never into a reconstructed code-only buffer.
"""
from __future__ import annotations

import re
from dataclasses import dataclass
from itertools import accumulate
from pathlib import Path


# =============================================================================
# Fences:  where the Agda code blocks are, and what prose precedes them
# =============================================================================

# A fence opener: ```agda, or an attribute form such as ```{.agda .hidden}.
_FENCE_OPEN = re.compile(r"^```\s*(?:agda\b|\{[^}]*\.agda[^}]*\})\s*$")
_FENCE_CLOSE = re.compile(r"^```\s*$")

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
    fence's opener, with HTML-comment delimiter lines removed.
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


def _strip_comment_delimiters(line: str) -> str:
    """Drop ``<!--`` / ``-->`` markers from a prose line, keeping any text that
    shares the line (the corpus has both solo delimiters around hidden fences
    and single-line ``<!-- note -->`` asides)."""
    return line.replace(_COMMENT_OPEN, " ").replace(_COMMENT_CLOSE, " ")


def _comment_depth_after(inside: bool, line: str) -> bool:
    """Are we inside an HTML comment after this prose line?  ``<!--`` and
    ``-->`` are not nestable in HTML, so a boolean suffices; a line carrying
    both (``<!-- aside -->``) leaves the state unchanged."""
    tail = line.rsplit(_COMMENT_CLOSE, 1)[-1] if _COMMENT_CLOSE in line else line
    if _COMMENT_OPEN in tail:
        return True
    if _COMMENT_CLOSE in line:
        return False
    return inside


def strip_front_matter(lines: tuple[str, ...]) -> tuple[str, ...]:
    """Drop a leading YAML front-matter block (``---`` … ``---``).

    Every module opens with Jekyll/MkDocs front matter (STYLE_GUIDE § "Jekyll/
    MkDocs YAML frontmatter").  It is metadata, never prose, so it must not
    count as the documentation preceding the first code fence.
    """
    if not lines or lines[0].strip() != "---":
        return lines
    for index, line in enumerate(lines[1:], 1):
        if line.strip() == "---":
            return lines[index + 1:]
    return lines


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
    in_fence = False
    open_line = 0
    hidden = False
    prose_start = 0
    for index, line in enumerate(lines):
        if in_fence:
            if _FENCE_CLOSE.match(line):
                out.append(Fence(
                    open_line=open_line + 1,
                    close_line=index + 1,
                    hidden=hidden,
                    body=tuple(lines[open_line + 1:index]),
                    prose=strip_front_matter(tuple(
                        _strip_comment_delimiters(p)
                        for p in lines[prose_start:open_line])),
                ))
                in_fence = False
                prose_start = index + 1
            continue
        if _FENCE_OPEN.match(line):
            in_fence, open_line, hidden = True, index, in_comment
            continue
        in_comment = _comment_depth_after(in_comment, line)
    return tuple(out)


# =============================================================================
# Literate extraction:  .lagda.md text -> one Agda line per source line
# =============================================================================

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
