#!/usr/bin/env python3
"""
File: scripts/python/barrels.py

Description: Keep slow-to-check modules out of barrels (issue #603).

  A *barrel* lets a reader import a family of modules at once, and defines
  nothing itself: once its comments and pragmas are set aside, its code is
  module headers (its own, and perhaps ``module _ {α : Level} where`` around
  an import that needs a parameter), import statements, and ``open``
  statements.  The full build does not need barrels, since ``make check``
  type-checks the generated aggregators, ``src/Everything.agda`` and
  ``src/EverythingLegacy.agda``, which import every module directly; so what
  a barrel imports is paid for only by whoever imports the barrel (Emacs on
  the root module, an agda-mcp load, a scratch file, a downstream library),
  and usually for an example they did not ask for.

  The policy (STYLE_GUIDE § "Barrels and slow modules") is as follows.  A
  module whose own check takes 3 s or more is *heavy*: its front matter says
  ``check-cost: heavy``, its prose states the cost, it stays in the build, and
  no barrel imports it.  A module that imports a heavy module, directly or
  through others, is heavy too, without a marker of its own.

  This checker reads the markers and never times anything, so CI stays
  deterministic.  It fails in the following cases:

  +  a barrel reaches a marked module through its imports (the report names
     the barrel, the import, and the chain from the barrel to the module);
  +  a marked module is missing from the generated aggregators, so the build
     no longer checks it;
  +  a ``check-cost`` entry the checker would not honor (a value other than
     ``heavy``, or a front-matter line that mentions the marker but is not
     read as it);
  +  a module it cannot classify (no front matter, no module header or one
     that disagrees with the path, an import statement it cannot parse, an
     ``import`` it did not read as a statement, an import of a library module
     with no file).  Each of these could hide a barrel, a marker, or an edge,
     so each is counted, printed, and fails.

  Barrels are found by the shape of their code, not by ``public``: eight of
  those outside ``Legacy/``, the root among them, import with a plain ``open
  import`` and re-export nothing, and they cost their importers the same.
  Imports before a parameterized header are allowed.  What is code is what
  Agda reads as code (``_utils/literate.py`` follows its reader of literate
  Markdown and its lexer's comments), so fences hidden in HTML comments are
  code; plain ``.agda`` modules under the root are read too, all of them code,
  though they have no front matter to carry a marker.

  The import graph spans the whole tree, ``Legacy/`` included, because the root
  module imports ``Legacy.Base`` and three other modules import Legacy modules.
  Legacy's own barrels are reported, not gated (``--include-legacy`` gates
  them): the tree is frozen, so the fix a failure there would ask for is an
  edit to frozen code, and every Legacy barrel is reached from ``Legacy.Base``,
  which the root imports, so a heavy module behind one of them already fails
  the gate at the root.

  The graph was validated against Agda's own: its transitive reduction is
  exactly the in-tree edges of ``agda --dependency-graph`` over both
  aggregators (604 edges among 344 modules, measured 2026-10-13).

  ``--audit LOG …`` is the cheap answer to a marker outliving the slowness it
  records.  It reads ``make PROFILE=modules profile`` logs (one run per log;
  the last table in a log is the one read) and lists the modules at or over
  the threshold without a marker, and the marked modules under it.  It never
  gates.  Given several logs it takes each module's least time, because a
  module's figure depends on the core that ran it: on a processor with
  performance and efficiency cores, ``Tables`` took 4.3 and 4.9 s pinned to a
  performance core and 9.3 and 10.3 s pinned to an efficiency core, and an
  unpinned module's figure varied 2.7-fold across three runs (measured
  2026-10-13).  Pinning the profile to a performance core (``taskset -c 2``)
  removes most of that.

Usage::

    python3 scripts/python/barrels.py                  # check src/
    python3 scripts/python/barrels.py --list           # and list the census
    python3 scripts/python/barrels.py --json           # machine-readable
    python3 scripts/python/barrels.py --audit run1.log run2.log run3.log

Exit status is 0 when clean, 1 when anything above fails, and 2 on a usage or
IO error (an unreadable module, aggregator, or log).

Design Principles:
  Pure core, effectful shell.  Classification, the graph, the chains and the
  audit are total functions of the texts read; reading files, printing and the
  exit status happen only in ``main``.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from enum import Enum
from itertools import takewhile
from pathlib import Path
from types import MappingProxyType
from typing import Mapping, Optional, Sequence

_SCRIPT_DIR = Path(__file__).resolve().parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))

from _utils import ErrorType, PipelineError, Result  # noqa: E402
from _utils.agda_imports import (  # noqa: E402
    ImportStmt,
    collect_statements,
    parse_statement,
    split_semicolons,
    take_balanced,
)
from _utils.file_ops import read_text  # noqa: E402
from _utils.literate import (  # noqa: E402
    clean_code_lines,
    file_code_lines,
    front_matter,
    front_matter_end,
    gather_files,
)


# =============================================================================
# The policy's constants
# =============================================================================

#: The front-matter entry that declares a module heavy, and its one value.
MARKER = "check-cost"
HEAVY = "heavy"

#: The policy's line, in seconds of a module's own check time in
#: ``make PROFILE=modules profile`` from an empty build.  Only ``--audit``
#: reads it; the gate reads markers.
THRESHOLD = 3.0

#: The frozen tree (ADR-001), read for the graph and gated only on request.
LEGACY = "Legacy"

#: The generated aggregators, which together are what ``make check`` checks.
AGGREGATORS = ("Everything.agda", "EverythingLegacy.agda")

_IMPORT_KEYWORDS = frozenset({"open import", "import"})


# =============================================================================
# Immutable data model
# =============================================================================

class Shape(Enum):
    """What a module's code consists of, apart from comments and pragmas."""

    BARREL = "barrel"              # the header and imports
    HEADER_ONLY = "header only"    # defines and imports nothing: nothing to check
    MODULE = "module"              # anything more


@dataclass(frozen=True)
class Edge:
    """One import statement: where it is, what it imports, and whether it
    re-exports (``public``)."""

    line: int
    target: str
    public: bool


@dataclass(frozen=True)
class Module:
    """One literate module, as far as the policy is concerned."""

    path: Path
    name: str
    shape: Shape
    imports: tuple[Edge, ...]      # every import statement, in source order
    marked: bool
    marker_line: int               # where the marker sits (1 when unmarked)

    @property
    def legacy(self) -> bool:
        return self.name.split(".")[0] == LEGACY


class Kind(Enum):
    """What a problem is about; every kind fails the gate."""

    BARREL = "barrel"              # a barrel reaches a heavy module
    BUILD = "build"                # a marked module is not in an aggregator
    MARKER = "marker"              # a check-cost entry the checker would not honor
    UNCLASSIFIED = "unclassified"  # a module the checker cannot read correctly


@dataclass(frozen=True)
class Problem:
    path: Path
    line: int
    kind: Kind
    message: str
    chain: tuple[str, ...] = ()

    def render(self) -> str:
        head = f"{self.path}:{self.line}: {self.message}"
        return head if not self.chain else head + "\n    chain: " + " → ".join(self.chain)

    def to_dict(self) -> dict[str, object]:
        return {"path": str(self.path), "line": self.line, "kind": self.kind.value,
                "message": self.message, "chain": list(self.chain)}


@dataclass(frozen=True)
class Tree:
    """Every module under the root, and what reading them turned up."""

    root: Path
    modules: Mapping[str, Module]
    graph: Mapping[str, tuple[str, ...]]   # imports within the tree, deduplicated
    problems: tuple[Problem, ...]          # markers and blind spots, from reading


@dataclass(frozen=True)
class Report:
    tree: Tree
    gated: tuple[Module, ...]              # the barrels the gate holds
    reported: tuple[Module, ...]           # Legacy's barrels, when not gated
    problems: tuple[Problem, ...]
    notes: tuple[Problem, ...]             # what a reported barrel would fail
    through: Mapping[str, tuple[str, ...]]  # heavy through imports: module -> chain


# =============================================================================
# Reading one module
# =============================================================================

def module_name(root: Path, path: Path) -> str:
    """The module a file under the include root defines, by Agda's rule."""
    relative = path.relative_to(root).as_posix()
    return relative.removesuffix(".lagda.md").removesuffix(".agda").replace("/", ".")


# Characters at which an Agda name ends, besides whitespace (a name may contain
# `-`, `'`, and most symbols, so a regex word boundary is not one).
_DELIMS = r"(){}⦃⦄;"

# A module header: the name, a telescope, and `where` as a token of its own
# (`module M (A : Set)where` is legal).  Any layout, since a parameterized
# header may span lines.
_HEADER = re.compile(rf"module\s+(?P<name>[^\s{_DELIMS}]+)(?P<telescope>.*?)"
                     rf"(?<![^\s{_DELIMS}])where(?![^\s{_DELIMS}])", re.DOTALL)

# A parameter that is not bracketed: a bare name (`ℓ`), or a modality or
# irrelevance mark before the next group (`@0`, `.`).
_BARE = re.compile(rf"[^\s{_DELIMS}]+")
_NOT_A_PARAMETER = re.compile(r"[:=→]|->")


def _binds_only(telescope: str) -> bool:
    """Is a header's telescope nothing but parameters?  Bracketed groups,
    ``(x : A)``, ``{𝑆 : Signature 𝓞 𝓥}``, ``⦃ _ : C ⦄``, and bare names,
    ``module M ℓ {A : Set ℓ} where``.  Recursion over the parameters."""
    rest = telescope.replace("⦃", "{").replace("⦄", "}").strip()
    if not rest:
        return True
    if rest[0] in "({":
        _, tail = take_balanced(rest)
        return _binds_only(tail)
    bare = _BARE.match(rest)
    return (bare is not None and not _NOT_A_PARAMETER.search(bare.group(0))
            and _binds_only(rest[bare.end():]))


@dataclass(frozen=True)
class _Statements:
    """A module's statements, sorted by what the classification needs."""

    imports: tuple[ImportStmt, ...]
    others: int                    # other code sharing a line with a statement
    unparsed: tuple[int, ...]      # lines of statements the parser could not read
    stray: tuple[int, ...]         # lines with an `import` read as no statement
    consumed: frozenset[int]       # 0-based lines the statements occupy


# What a statement begins with; a `;`-separated piece that does not is other
# code on the statement's line (`open R ; p = lhs e` in a `where` block).  And
# the keyword `import` anywhere, as a token (`import-all` is a name).
_STATEMENT_START = re.compile(rf"(?:open|import)(?![^\s{_DELIMS}])")
_IMPORT_TOKEN = re.compile(rf"(?<![^\s{_DELIMS}])import(?![^\s{_DELIMS}])")


def _statements(code: list[str]) -> _Statements:
    """Every import/open statement in the comment-free code, and every
    ``import`` the statements do not account for.  The collector reads a
    statement only where it begins a line, so ``private open import M``, or
    ``module _ where open import M``, is not one; the import would be an edge
    missing from the graph, so its line is reported instead."""
    raws = collect_statements(code)
    consumed = frozenset(i for _, span, _ in raws for i in span)
    pieces = [(start, piece, parse_statement(start, piece))
              for start, _, joined in raws for piece in split_semicolons(joined)]
    return _Statements(
        imports=tuple(s for _, _, s in pieces if s and s.keyword in _IMPORT_KEYWORDS),
        others=sum(1 for _, piece, s in pieces
                   if s is None and not _STATEMENT_START.match(piece)),
        unparsed=tuple(start for start, piece, s in pieces
                       if s is None and _STATEMENT_START.match(piece)),
        stray=tuple(sorted(
            {start for start, piece, s in pieces
             if s is None and not _STATEMENT_START.match(piece)
             and _IMPORT_TOKEN.search(piece)}
            | {index + 1 for index, line in enumerate(code)
               if index not in consumed and _IMPORT_TOKEN.search(line)})),
        consumed=consumed,
    )


def _headers_only(code: str) -> bool:
    """Is ``code`` nothing but module headers whose telescopes only bind?  The
    top-level header comes first; a further one opens a nested module, as
    ``module _ {α : Level} where`` does around an import that needs a level."""
    rest = code.strip()
    if not rest:
        return True
    header = _HEADER.match(rest)
    return (header is not None and _binds_only(header.group("telescope"))
            and _headers_only(rest[header.end():]))


def _shape(residual: str, statements: _Statements) -> Shape:
    """The shape of a module whose code, less its statements, is ``residual``.
    A barrel defines nothing: what is left once its import and ``open``
    statements are gone is module headers, and no other code shares a
    statement's line.  (An ``open`` defines nothing either: ``import M`` and
    ``open M public`` re-export what ``open import M public`` does.)

    Such a module that imports nothing is header-only rather than a barrel,
    whatever it opens: Agda refuses ``open M`` unless ``M`` is imported
    (``NoSuchModule``), except for ``Agda.Primitive``, which it imports
    implicitly and which lies outside the tree.  Every edge of the graph is
    an import, so a module without one reaches nothing, and the gate has
    nothing to hold it to."""
    if not (_headers_only(residual) and statements.others == 0):
        return Shape.MODULE
    return Shape.BARREL if statements.imports else Shape.HEADER_ONLY


# The marker as the front-matter reader reads it: the key at the start of the
# line, exactly so spelled (see _utils.literate.front_matter).
_MARKER_ENTRY = re.compile(rf"{MARKER}\s*:.*")


def _marker_problems(path: Path, text: str) -> tuple[tuple[bool, int], tuple[Problem, ...]]:
    """Whether a module is marked (and on which line), and any front-matter line
    the checker would not honor.  A line that mentions the marker in any
    spelling (`check_cost`, `Check-Cost`, `check cost`, an indented or quoted
    key) but is not read as it would be silently ignored, so it is reported."""
    lines = text.split("\n")
    end = front_matter_end(lines)
    if end == 0:
        return (False, 1), (Problem(
            path, 1, Kind.UNCLASSIFIED,
            "no front matter (the first line is not `---`, or the block never "
            "closes), so a check-cost marker here could not be read"),)
    block = [(index + 1, line) for index, line in enumerate(lines[1:end - 1], 1)]
    read = [number for number, line in block if _MARKER_ENTRY.fullmatch(line)]
    marker_line = read[-1] if read else 1    # the last one wins, as in YAML
    misread = tuple(
        Problem(path, number, Kind.MARKER,
                f"`{line.strip()}` mentions the marker but is not read as it; "
                f"write `{MARKER}: {HEAVY}` at the start of a line")
        for number, line in block
        if "checkcost" in re.sub(r"[^a-z]", "", line.lower())
        and not _MARKER_ENTRY.fullmatch(line))
    value = front_matter(text).get(MARKER)
    unknown = (() if value is None or value == HEAVY else (Problem(
        path, marker_line, Kind.MARKER,
        f"`{MARKER}: {value}` is not a value the policy defines; the only one is `{HEAVY}`"),))
    return (value == HEAVY, marker_line), misread + unknown


def scan_module(root: Path, path: Path, text: str) -> tuple[Module, tuple[Problem, ...]]:
    """Classify one module and collect what about it the checker cannot honor.
    A plain ``.agda`` module is code throughout and has no front matter, so it
    cannot be marked, and is not asked for a marker it could not carry."""
    name = module_name(root, path)
    literate = path.name.endswith(".lagda.md")
    code = file_code_lines(text) if literate else clean_code_lines(text.split("\n"))
    statements = _statements(code)
    rest = [(index + 1, line) for index, line in enumerate(code)
            if index not in statements.consumed and line.strip()]
    residual = "\n".join(line for _, line in rest).strip()
    first = rest[0][0] if rest else 1        # where the code after the imports begins
    header = _HEADER.match(residual)
    (marked, marker_line), marker_problems = (
        _marker_problems(path, text) if literate else ((False, 1), ()))
    header_problems = (
        (Problem(path, first, Kind.UNCLASSIFIED,
                 "no top-level module header found where the code begins"),)
        if header is None else
        (Problem(path, first, Kind.UNCLASSIFIED,
                 f"the header declares `{header.group('name')}`, but the path "
                 f"makes the module `{name}`"),)
        if header.group("name") != name else ())
    unparsed = tuple(Problem(path, line, Kind.UNCLASSIFIED,
                             "an import or open statement the parser cannot read")
                     for line in statements.unparsed)
    stray = tuple(Problem(path, line, Kind.UNCLASSIFIED,
                          "an `import` the parser does not read as a statement; "
                          "begin a line with it")
                  for line in statements.stray)
    module = Module(
        path=path, name=name,
        # A module the checker cannot classify is treated as an ordinary one,
        # and the problem above says so.
        shape=_shape(residual, statements) if header else Shape.MODULE,
        imports=tuple(Edge(s.line, s.module, s.public) for s in statements.imports),
        marked=marked, marker_line=marker_line)
    return module, marker_problems + header_problems + unparsed + stray


def scan_tree(root: Path, sources: Sequence[tuple[Path, str]]) -> Tree:
    """Read every module and build the import graph within the tree.

    An import whose module has no file is outside the tree (the standard
    library) unless its first segment is one of the tree's own top-level
    names, in which case it is a module that should be here and is not.
    """
    scanned = [scan_module(root, path, text) for path, text in sources]
    modules = MappingProxyType({m.name: m for m, _ in scanned})
    namespaces = frozenset(name.split(".")[0] for name in modules)
    missing = tuple(
        Problem(m.path, edge.line, Kind.UNCLASSIFIED,
                f"imports `{edge.target}`, which names no module under {root}")
        for m in modules.values() for edge in m.imports
        if edge.target not in modules and edge.target.split(".")[0] in namespaces)
    graph = MappingProxyType({
        m.name: tuple(dict.fromkeys(e.target for e in m.imports if e.target in modules))
        for m in modules.values()})
    return Tree(root, modules, graph,
                tuple(p for _, ps in scanned for p in ps) + missing)


# =============================================================================
# The graph:  which modules reach a marked one, and by what chain
# =============================================================================

def nearest_marked(start: str, graph: Mapping[str, tuple[str, ...]],
                   marked: frozenset[str]) -> Optional[tuple[str, ...]]:
    """The shortest import chain from ``start`` to a marked module, both ends
    included, or ``None``.  Breadth first, so the chain is a shortest one, and
    imports are followed in source order, so the answer is deterministic.  The
    ``seen`` set makes it total on a cyclic graph, which Agda would refuse but
    a misparse could produce."""
    def search(frontier: tuple[tuple[str, ...], ...],
               seen: frozenset[str]) -> Optional[tuple[str, ...]]:
        hit = next((chain for chain in frontier if chain[-1] in marked), None)
        if hit is not None or not frontier:
            return hit
        reached = [(nxt, chain + (nxt,)) for chain in frontier
                   for nxt in graph.get(chain[-1], ()) if nxt not in seen]
        # The first chain to reach each new module, in the order reached: a
        # dict built from the reversed list keeps each module's first chain.
        first = dict(reversed(reached))
        fresh = tuple(first[name] for name in dict.fromkeys(n for n, _ in reached))
        return search(fresh, seen | frozenset(first))
    return search(((start,),), frozenset({start}))


def barrel_problems(module: Module, tree: Tree,
                    marked: frozenset[str]) -> tuple[Problem, ...]:
    """One problem per import of a barrel that reaches a marked module."""
    return tuple(
        Problem(module.path, edge.line, Kind.BARREL,
                f"barrel `{module.name}` imports `{edge.target}`, which "
                + (f"is heavy (`{MARKER}: {HEAVY}`)" if len(chain) == 1 else
                   f"reaches the heavy module `{chain[-1]}`"),
                (module.name,) + chain)
        for edge in module.imports if edge.target in tree.modules
        for chain in [nearest_marked(edge.target, tree.graph, marked)]
        if chain is not None)


def build_problems(tree: Tree, built: frozenset[str],
                   aggregators: Sequence[Path]) -> tuple[Problem, ...]:
    """Marked modules the aggregators do not import: the build would no longer
    check them, which is the one thing the policy promises it still does."""
    named = ", ".join(str(a) for a in aggregators)
    return tuple(
        Problem(m.path, m.marker_line, Kind.BUILD,
                f"`{m.name}` is marked heavy but missing from {named}; a heavy "
                "module leaves the barrels, never the build")
        for m in tree.modules.values() if m.marked and m.name not in built)


def marked_names(tree: Tree) -> frozenset[str]:
    return frozenset(name for name, m in tree.modules.items() if m.marked)


def heavy_through(tree: Tree) -> Mapping[str, tuple[str, ...]]:
    """The unmarked modules that are heavy because of what they import, each
    with a shortest chain to a marked module."""
    marked = marked_names(tree)
    return MappingProxyType({
        name: chain for name in sorted(tree.modules) if name not in marked
        for chain in [nearest_marked(name, tree.graph, marked)] if chain is not None})


def check(tree: Tree, built: frozenset[str], aggregators: Sequence[Path],
          gate_legacy: bool) -> Report:
    """The whole verdict, as a value."""
    marked = marked_names(tree)
    barrels = tuple(m for m in tree.modules.values() if m.shape is Shape.BARREL)
    gated = tuple(m for m in barrels if gate_legacy or not m.legacy)
    reported = tuple(m for m in barrels if m.legacy and not gate_legacy)
    return Report(
        tree=tree, gated=gated, reported=reported,
        problems=(tuple(p for m in gated for p in barrel_problems(m, tree, marked))
                  + build_problems(tree, built, aggregators)
                  + tree.problems),
        notes=tuple(p for m in reported for p in barrel_problems(m, tree, marked)),
        through=heavy_through(tree))


# =============================================================================
# The aggregators
# =============================================================================

_AGGREGATED = re.compile(r"import\s+(\S+)\s*")


def aggregated(text: str) -> frozenset[str]:
    """The modules a generated aggregator imports, one ``import M`` per line."""
    return frozenset(m.group(1) for line in text.split("\n")
                     if (m := _AGGREGATED.fullmatch(line)))


# =============================================================================
# The audit:  a profile against the markers
# =============================================================================

# A row of the `--profile=modules` table: a name, then its time in
# milliseconds, which Agda prints with thousands separators (`5,242ms`).  The
# table opens with a `Total` row and carries a `Miscellaneous` one, neither of
# them a module; rows under 10 ms are not printed at all.
_PROFILE_ROW = re.compile(r"(?P<name>\S+)\s+(?P<ms>\d[\d,]*)ms\s*")
_NOT_MODULES = frozenset({"Total", "Miscellaneous"})


def profile_times(log: str) -> Result[Mapping[str, float], PipelineError]:
    """Each profiled module's own check time, in seconds, from the table that
    begins at the log's last ``Total`` row."""
    lines = log.split("\n")
    starts = [index for index, line in enumerate(lines)
              if (m := _PROFILE_ROW.fullmatch(line)) and m.group("name") == "Total"]
    if not starts:
        return Result.err(PipelineError(
            ErrorType.PARSING_ERROR,
            "no `Total` row: not the log of `make PROFILE=modules profile`"))
    # The table is one contiguous run of rows.
    rows = takewhile(bool, (_PROFILE_ROW.fullmatch(line) for line in lines[starts[-1]:]))
    return Result.ok(MappingProxyType({
        m.group("name"): int(m.group("ms").replace(",", "")) / 1000
        for m in rows if m.group("name") not in _NOT_MODULES}))


def least_times(runs: Sequence[Mapping[str, float]]) -> Mapping[str, float]:
    """Each module's least time across the runs whose tables list it.  Load
    only ever adds time, so the least is the best estimate of a module's own
    cost; a module a table omits ran under 10 ms there, or was not checked."""
    names = sorted({name for run in runs for name in run})
    return MappingProxyType({name: min(run[name] for run in runs if name in run)
                             for name in names})


@dataclass(frozen=True)
class Audit:
    threshold: float
    runs: int                                     # profile logs read
    profiled: int                                 # module rows in the tables
    unmarked_over: tuple[tuple[str, float], ...]  # at or over, no marker
    marked_under: tuple[tuple[str, float], ...]   # marked, under
    marked_absent: tuple[str, ...]                # marked, no row
    outside: int                                  # rows naming no module of the tree


def audit(tree: Tree, runs: Sequence[Mapping[str, float]], threshold: float) -> Audit:
    """Compare profiles with the markers.  Advisory: the markers are what the
    gate reads, and profile runs are the evidence for changing one."""
    modules = tree.modules
    times = least_times(runs)
    by_time = sorted(times.items(), key=lambda item: (-item[1], item[0]))
    return Audit(
        threshold=threshold,
        runs=len(runs),
        profiled=len(times),
        unmarked_over=tuple((n, t) for n, t in by_time
                            if n in modules and not modules[n].marked and t >= threshold),
        marked_under=tuple((n, t) for n, t in by_time
                           if n in modules and modules[n].marked and t < threshold),
        marked_absent=tuple(sorted(n for n, m in modules.items()
                                   if m.marked and n not in times)),
        outside=sum(1 for n in times if n not in modules))


# =============================================================================
# Rendering
# =============================================================================

def _plural(count: int, word: str) -> str:
    return f"{count} {word}{'' if count == 1 else 's'}"


def summary(report: Report) -> str:
    """The closing line: the census, then the verdict by kind."""
    tree = report.tree
    modules = tree.modules.values()
    legacy = sum(1 for m in modules if m.legacy)
    header_only = sum(1 for m in modules if m.shape is Shape.HEADER_ONLY)
    marked = sum(1 for m in modules if m.marked)
    by_kind = {kind: sum(1 for p in report.problems if p.kind is kind) for kind in Kind}
    reported = (f", {len(report.reported)} in {LEGACY}/ reported only"
                if report.reported else "")
    return (
        f"Scanned {len(tree.modules)} modules under {tree.root} ({legacy} in {LEGACY}/): "
        f"{_plural(len(report.gated) + len(report.reported), 'barrel')} "
        f"({len(report.gated)} gated{reported}), {header_only} header-only; "
        f"{marked} marked heavy, {len(report.through)} heavy through imports; "
        f"{_plural(len(report.problems), 'problem')} "
        f"({by_kind[Kind.BARREL]} barrel, {by_kind[Kind.BUILD]} build, "
        f"{by_kind[Kind.MARKER]} marker, "
        f"{by_kind[Kind.UNCLASSIFIED]} cannot classify).")


def census(report: Report) -> list[str]:
    """The ``--list`` section: barrels, marked modules, and the modules heavy
    through their imports, each with what makes it so."""
    def barrel_row(m: Module) -> str:
        public = sum(1 for e in m.imports if e.public)
        exports = ("re-exports all" if public == len(m.imports) else
                   "re-exports none" if public == 0 else f"re-exports {public}")
        return f"  {m.name}  ({_plural(len(m.imports), 'import')}, {exports})"
    gated = sorted(report.gated, key=lambda m: m.name)
    reported = sorted(report.reported, key=lambda m: m.name)
    marked = sorted(n for n, m in report.tree.modules.items() if m.marked)
    return (
        [f"Barrels, gated ({len(gated)}):"] + [barrel_row(m) for m in gated]
        + ([f"Barrels in {LEGACY}/, reported only ({len(reported)}):"]
           + [barrel_row(m) for m in reported] if reported else [])
        + [f"Marked heavy ({len(marked)}):"] + [f"  {n}" for n in marked]
        + [f"Heavy through imports ({len(report.through)}):"]
        + [f"  {n}  ({' → '.join(c)})" for n, c in report.through.items()])


def report_json(report: Report) -> str:
    modules = report.tree.modules.values()
    return json.dumps({
        "root": str(report.tree.root),
        "modules": len(report.tree.modules),
        "barrels": [{"module": m.name, "path": str(m.path), "gated": m in report.gated,
                     "imports": [{"line": e.line, "module": e.target, "public": e.public}
                                 for e in m.imports]}
                    for m in sorted(report.gated + report.reported, key=lambda m: m.name)],
        "header_only": sorted(m.name for m in modules if m.shape is Shape.HEADER_ONLY),
        "marked": sorted(m.name for m in modules if m.marked),
        "heavy_through_imports": {n: list(c) for n, c in report.through.items()},
        "problems": [p.to_dict() for p in report.problems],
        "notes": [p.to_dict() for p in report.notes],
    }, ensure_ascii=False, indent=2)


def render_audit(result: Audit, logs: Sequence[Path], tree: Tree,
                 through: Mapping[str, tuple[str, ...]]) -> list[str]:
    def rows(items: Sequence[tuple[str, float]], why: bool) -> list[str]:
        if not items:
            return ["    (none)"]
        return [f"    {n}  {t:.2f} s"
                + (f"  (heavy already, through `{through[n][-1]}`)"
                   if why and n in through else "")
                for n, t in items]
    t = f"{result.threshold:g} s"
    source = (f"{logs[0]}" if result.runs == 1 else
              f"{result.runs} logs, each module at its least time across them")
    return (
        [f"Audit of {source}: {result.profiled} profiled modules (Agda omits rows "
         f"under 10 ms), threshold {t}."]
        + [f"  unmarked, at or over {t}:"] + rows(result.unmarked_over, True)
        + [f"  marked, under {t}:"] + rows(result.marked_under, False)
        + ["  marked, with no row (not checked in that run, or under 10 ms):"]
        + ([f"    {n}" for n in result.marked_absent] or ["    (none)"])
        + ([f"  {_plural(result.outside, 'row')} "
            f"{'names' if result.outside == 1 else 'name'} no module under "
            f"{tree.root} (the aggregator, say)."] if result.outside else []))


# =============================================================================
# Driver
# =============================================================================

def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Fail when a barrel module reaches a module marked "
                    "`check-cost: heavy`, or when a marked module leaves the "
                    "build (issue #603).")
    parser.add_argument("root", nargs="?", default="src",
                        help="the include root (default: src).  The whole tree "
                             "is read, Legacy included, since a barrel's cost is "
                             "everything it imports transitively")
    parser.add_argument("--everything", action="append", metavar="FILE",
                        help="a generated aggregator; repeatable (default: "
                             "Everything.agda and EverythingLegacy.agda in the root)")
    parser.add_argument("--include-legacy", action="store_true",
                        help="also gate the barrels of the frozen Legacy tree "
                             "(reported, not gated, by default)")
    parser.add_argument("--list", action="store_true",
                        help="list the barrels, the marked modules, and the "
                             "modules heavy through their imports")
    parser.add_argument("--json", action="store_true",
                        help="emit the census and the problems as JSON")
    parser.add_argument("--exit-zero", action="store_true",
                        help="always exit 0 (do not signal problems)")
    parser.add_argument("--audit", nargs="+", metavar="LOG",
                        help="instead of the check, compare `make PROFILE=modules "
                             "profile` logs with the markers, taking each module's "
                             "least time across them (never gates)")
    parser.add_argument("--threshold", type=float, default=THRESHOLD, metavar="SECONDS",
                        help="the audit's line (default: %(default)g)")
    return parser


def read_all(files: Sequence[Path]) -> tuple[list[tuple[Path, str]], list[tuple[Path, PipelineError]]]:
    """IO boundary: read every file in the Result monad, splitting successes
    from failures so a bad read is reported rather than raised."""
    reads = [(f, read_text(f)) for f in files]
    return ([(f, r.unwrap()) for f, r in reads if r.is_ok],
            [(f, r.unwrap_err()) for f, r in reads if r.is_err])


def main(argv: list[str]) -> int:
    args = build_parser().parse_args(argv)
    root = Path(args.root)
    if not root.is_dir():
        sys.stderr.write(f"error: {root} is not a directory\n")
        return 2
    # Literate modules, and plain ones, which the Makefile's aggregators build
    # too; the aggregators themselves are not modules of the library.
    plain = sorted(p for p in root.rglob("*.agda")
                   if not (p.parent == root and p.name in AGGREGATORS))
    sources, failures = read_all(gather_files([root], include_legacy=True) + plain)
    for _, error in failures:
        sys.stderr.write(f"error: {error.message}\n")
    if failures or not sources:
        if not sources:
            sys.stderr.write(f"error: no modules under {root}\n")
        return 2
    tree = scan_tree(root, sources)

    if args.audit:
        logs = [Path(log) for log in args.audit]
        runs = [(log, read_text(log).and_then(profile_times)) for log in logs]
        for log, run in runs:
            if run.is_err:
                sys.stderr.write(f"error: {log}: {run.unwrap_err().message}\n")
        if any(run.is_err for _, run in runs):
            return 2
        result = audit(tree, [run.unwrap() for _, run in runs], args.threshold)
        print("\n".join(render_audit(result, logs, tree, heavy_through(tree))))
        return 0

    aggregators = [Path(p) for p in (args.everything or [root / a for a in AGGREGATORS])]
    reads, unreadable = read_all(aggregators)
    for path, error in unreadable:
        sys.stderr.write(f"error: {path}: {error.message} (run `make Everything.agda "
                         "EverythingLegacy.agda`, or name the aggregators with --everything)\n")
    if unreadable:
        return 2
    built = frozenset().union(*(aggregated(text) for _, text in reads))
    report = check(tree, built, aggregators, args.include_legacy)

    if args.json:
        print(report_json(report))
    else:
        lines = ([p.render() for p in report.problems]
                 + [f"note ({LEGACY}/, reported only): " + p.render() for p in report.notes]
                 + (census(report) if args.list else [])
                 + [summary(report)])
        print("\n".join(lines))
    return 0 if (args.exit_zero or not report.problems) else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
