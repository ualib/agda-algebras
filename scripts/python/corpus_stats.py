#!/usr/bin/env python3
"""
File: scripts/python/corpus_stats.py

Description: The landing page's headline figures, counted from the tree,
  written back into the source, and gated in CI (issue #575).

  ``docs/index.md`` opens with a strip of four numbers: how many literate
  modules the library holds, how many lines of Agda they contain, what share of
  them is machine-checked, and which toolchain checks them.  Every one of those
  is a fact about this repository, so none of them should be typed by hand.

  They were, and it showed.  ``mkdocs_hooks.py`` substituted the two counted
  figures into the *rendered* page at build time and never wrote them back, so
  the values committed in ``docs/index.md`` stayed at their 2026-07-28 reading
  (302 modules, 60k lines) while the library grew to 339 modules and 67k lines.
  Anyone reading this repository on GitHub rather than at the deployed site read
  July's figures for six weeks, and the stale pair was quoted elsewhere as
  current.

  This module is the fix, and it is used three ways:

    +  ``corpus_stats.py``          refresh the markers in ``docs/index.md``
       (``make corpus-stats``);
    +  ``corpus_stats.py --check``  fail, with a diff, when a committed value
       has drifted (``make corpus-stats-check``, which the *Landing-page stats*
       CI job runs, so a pull request that moves a number cannot merge without
       refreshing the page);
    +  ``corpus_stats.py --json``   emit the figures as one JSON record, for
       anything outside this repository that wants to quote them rather than
       hand-copy them.

  ``mkdocs_hooks.py`` imports :func:`landing_values` and :func:`fill` for its
  build-time substitution, so the deployed site and the committed source are
  computed by one function and cannot disagree.

Design Principles:
  Every figure names a source of truth and is read from it, never restated:

    +  ``modules``, ``loc`` and ``checked`` come from the canonical tree,
       ``src/`` minus the frozen ``Legacy/``.  That is exactly the set of
       modules CI type-checks, between the *Type-check library* and *Type-check
       certificates* jobs.
    +  ``agda`` and ``stdlib`` come from ``mkdocs.yml``'s ``extra:`` site
       variables, which the tool reconciles in turn against the two pins that
       actually bind: ``agda-algebras.agda-lib``'s ``depend:`` line, whose
       stdlib version Agda enforces exactly, and ``flake.nix``'s version-floor
       guards, which state the series the dev shell expects.  Bumping the
       toolchain without updating the docs therefore fails the check.

  A source of truth that cannot be read is an error, never a skipped check.  If
  one of those files is reshaped so a pattern stops matching, the tool says
  which pattern and exits non-zero rather than quietly passing; a check that
  silently measures nothing is how the stale number survived six weeks.
"""
from __future__ import annotations

import argparse
import difflib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Mapping, Sequence

# Import the shared utilities the way the sibling scripts do: make this file's
# directory importable, then pull in the Result monad, the pure file-reading
# wrappers, and the literate front end.
_SCRIPT_DIR = Path(__file__).resolve().parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))

from _utils import ErrorType, PipelineError, Result, sequence_results  # noqa: E402
from _utils.file_ops import read_text, write_text  # noqa: E402
from _utils.literate import fences  # noqa: E402

# -- Sources of truth ---------------------------------------------------------

SRC = Path("src")
LEGACY = "Legacy"                       # the frozen tree, excluded (ADR-001)
LIB = Path("agda-algebras.agda-lib")
FLAKE = Path("flake.nix")
MKDOCS = Path("mkdocs.yml")

# The pages carrying stat markers.  Only the landing page does today; the tool
# loops, so a second page costs one line.  Every page listed here must carry
# every marker the tool computes (see `unfilled`).
PAGES: tuple[Path, ...] = (Path("docs/index.md"),)

# <!-- ualib:stat:NAME -->value<!-- /ualib:stat:NAME -->.  DOTALL so the markers
# keep matching if a page is reformatted with the comments on separate lines;
# the \1 backreference pins each pair to its own name.
STAT = re.compile(r"<!-- ualib:stat:(\w+) -->.*?<!-- /ualib:stat:\1 -->", re.DOTALL)


# =============================================================================
# What the tree holds
# =============================================================================

@dataclass(frozen=True)
class Corpus:
    """The canonical tree in three numbers: how many literate modules it holds,
    how many lines of Agda they contain, and how many of them are checked under
    ``--safe`` (so nothing in them is postulated, assumed terminating, or built
    on an unsafe primitive)."""

    modules: int
    loc: int
    safe: int


@dataclass(frozen=True)
class Toolchain:
    """The Agda and standard-library versions the library is checked against."""

    agda: str
    stdlib: str


@dataclass(frozen=True)
class Stats:
    """Everything the landing page advertises."""

    corpus: Corpus
    toolchain: Toolchain

    @property
    def markers(self) -> dict[str, str]:
        """The string each ``ualib:stat`` marker should hold."""
        c, t = self.corpus, self.toolchain
        return {
            "modules": str(c.modules),
            # Half-up rounding to thousands.  round() rounds ties to even, so
            # 60_500 would render as "60k"; a reader of a "…k" stat expects 61k.
            "loc": f"{(c.loc + 500) // 1000}k",
            # Floor, never round: 338 of 339 must not print as "100%".
            "checked": f"{100 * c.safe // c.modules if c.modules else 0}%",
            "agda": t.agda,
            "stdlib": t.stdlib,
        }

    @property
    def record(self) -> dict[str, object]:
        """The JSON record: the raw counts alongside the rendered markers."""
        return {
            "modules": self.corpus.modules,
            "loc": self.corpus.loc,
            "safe": self.corpus.safe,
            "agda": self.toolchain.agda,
            "stdlib": self.toolchain.stdlib,
            "markers": self.markers,
        }


# The module's OPTIONS pragma.  `[^#]*` stops at the closing `#-}` and cannot
# run past it into the body.
_OPTIONS = re.compile(r"\{-#\s*OPTIONS\b([^#]*)#-\}")


def module_stats(text: str) -> tuple[int, bool]:
    """``(lines of Agda, checked under --safe)`` for one literate module.

    One pass over the fences serves both: the lines are everything between the
    fence delimiters of the module's ```` ```agda ```` blocks (the hidden
    preamble fence counts, because Agda checks it; prose and the delimiters
    themselves do not), and the pragma is read from that same code, so an
    OPTIONS line quoted in prose cannot be mistaken for the module's own.
    """
    blocks = fences(text)
    code = "\n".join(line for block in blocks for line in block.body)
    pragma = _OPTIONS.search(code)
    return (sum(len(block.body) for block in blocks),
            pragma is not None and "--safe" in pragma.group(1).split())


def corpus(texts: Sequence[str]) -> Corpus:
    """Aggregate the per-module numbers."""
    per_module = [module_stats(text) for text in texts]
    return Corpus(modules=len(per_module),
                  loc=sum(loc for loc, _ in per_module),
                  safe=sum(1 for _, safe in per_module if safe))


def canonical_modules(src: Path = SRC) -> list[Path]:
    """The modules the landing page counts: every literate module under ``src/``
    except the frozen ``Legacy/`` tree (ADR-001).  That is the union of the two
    walks the Makefile's ``find`` makes for ``Everything.agda`` and
    ``EverythingCertificates.agda``, so every module counted here is one CI
    type-checks."""
    return sorted(p for p in src.rglob("*.lagda.md")
                  if p.relative_to(src).parts[0] != LEGACY)


def measure(src: Path = SRC) -> Result[Corpus, PipelineError]:
    """Read and count the canonical tree."""
    return sequence_results([read_text(p) for p in canonical_modules(src)]).map(corpus)


# =============================================================================
# What the toolchain pins say
# =============================================================================

# mkdocs.yml's `extra:` site variables (two-space indented under `extra:`).
_EXTRA_AGDA = re.compile(r"^\s+agda_version:\s*\"?([0-9][0-9.]*)\"?\s*$", re.MULTILINE)
_EXTRA_STDLIB = re.compile(r"^\s+stdlib_version:\s*\"?([0-9][0-9.]*)\"?\s*$", re.MULTILINE)

# agda-algebras.agda-lib's `depend: standard-library-2.3`.  Agda resolves an
# exact-version dependency exactly, so this is the pin that binds.
_DEPEND_STDLIB = re.compile(r"^depend:.*\bstandard-library-([0-9][0-9.]*)", re.MULTILINE)


def _guard(var: str) -> re.Pattern[str]:
    """flake.nix's version-floor guard for a shell variable.  The dev shell
    warns when the realized toolchain leaves the expected series::

        case "${agdaVer}" in
          2.8.*) : ;;

    and this captures that series (``2.8``), which the version the docs declare
    must belong to."""
    return re.compile(r'case\s+"\$\{' + var + r'\}"\s+in\s+([0-9][0-9.]*?)\.?\*\)')


def _field(text: str, pattern: re.Pattern[str], what: str,
           where: Path) -> Result[str, PipelineError]:
    """The first capture of ``pattern`` in ``text``, or an error naming what was
    being read and from where.  A source of truth that has moved must fail the
    check loudly rather than drop out of it."""
    match = pattern.search(text)
    if match is None:
        return Result.err(PipelineError(
            ErrorType.PARSING_ERROR,
            f"could not read {what} from {where}; the file's shape changed, so "
            f"scripts/python/corpus_stats.py needs updating",
            context={"pattern": pattern.pattern}))
    return Result.ok(match.group(1))


def _in_series(version: str, series: str) -> bool:
    """Whether ``version`` (2.8.0) belongs to ``series`` (2.8)."""
    return version == series or version.startswith(series + ".")


def _reconcile(fields: Sequence[str]) -> Result[Toolchain, PipelineError]:
    """Cross-check the toolchain the docs declare against the pins that bind it."""
    agda, stdlib, pinned, agda_series, stdlib_series = fields
    checks = (
        (stdlib == pinned,
         f"{MKDOCS} says stdlib {stdlib}, but {LIB} depends on "
         f"standard-library-{pinned}"),
        (_in_series(agda, agda_series),
         f"{MKDOCS} says Agda {agda}, but {FLAKE} guards the {agda_series} series"),
        (_in_series(pinned, stdlib_series),
         f"{LIB} depends on standard-library-{pinned}, but {FLAKE} guards the "
         f"{stdlib_series} series"),
    )
    disagreements = [why for holds, why in checks if not holds]
    if disagreements:
        return Result.err(PipelineError(
            ErrorType.VALIDATION_ERROR,
            "the declared toolchain disagrees with the pins:\n  "
            + "\n  ".join(disagreements)))
    return Result.ok(Toolchain(agda=agda, stdlib=stdlib))


def toolchain(mkdocs_text: str, lib_text: str,
              flake_text: str) -> Result[Toolchain, PipelineError]:
    """The toolchain the landing page should advertise, read from the three
    files that declare it and reconciled across them."""
    return sequence_results([
        _field(mkdocs_text, _EXTRA_AGDA, "extra.agda_version", MKDOCS),
        _field(mkdocs_text, _EXTRA_STDLIB, "extra.stdlib_version", MKDOCS),
        _field(lib_text, _DEPEND_STDLIB, "the standard-library version in depend:", LIB),
        _field(flake_text, _guard("agdaVer"), "the Agda version-floor guard", FLAKE),
        _field(flake_text, _guard("stdlibVer"), "the stdlib version-floor guard", FLAKE),
    ]).and_then(_reconcile)


def read_toolchain(mkdocs: Path = MKDOCS, lib: Path = LIB,
                   flake: Path = FLAKE) -> Result[Toolchain, PipelineError]:
    """Read the three declaring files and reconcile them."""
    return sequence_results([read_text(mkdocs), read_text(lib), read_text(flake)]) \
        .and_then(lambda texts: toolchain(*texts))


def measure_all(src: Path = SRC) -> Result[Stats, PipelineError]:
    """Everything the landing page advertises, counted and read."""
    return measure(src).and_then(
        lambda c: read_toolchain().map(lambda t: Stats(corpus=c, toolchain=t)))


def landing_values(src: Path = SRC) -> Result[dict[str, str], PipelineError]:
    """The stat-marker values for the landing page.  This is what the MkDocs
    hook substitutes at build time and what ``--check`` holds the committed file
    to, so the site and the source are one computation."""
    return measure_all(src).map(lambda s: s.markers)


# =============================================================================
# The pages that carry the markers
# =============================================================================

def fill(markdown: str, values: Mapping[str, str]) -> str:
    """Rewrite every known stat marker to hold its counted value.

    The markers are preserved rather than consumed, because the same
    substitution serves the committed source (where they must survive to be
    refreshed again) and the rendered page (where an HTML comment is invisible).
    A marker the tool does not compute is left exactly as it stands.
    """
    def value(match: re.Match[str]) -> str:
        name = match.group(1)
        if name not in values:
            return match.group(0)
        return f"<!-- ualib:stat:{name} -->{values[name]}<!-- /ualib:stat:{name} -->"

    return STAT.sub(value, markdown)


def marker_names(text: str) -> set[str]:
    """The stat markers a page carries."""
    return {match.group(1) for match in STAT.finditer(text)}


def unfilled(text: str, values: Mapping[str, str]) -> tuple[str, ...]:
    """Markers the tool computes that the page does not carry.  A renamed or
    misspelled marker would otherwise leave a hand-typed number standing while
    the check reported success, which is exactly the failure this tool exists to
    end."""
    return tuple(sorted(set(values) - marker_names(text)))


@dataclass(frozen=True)
class PageDrift:
    """One page, as committed and as it would be with the counted values in it."""

    path: Path
    committed: str
    refreshed: str

    @property
    def stale(self) -> bool:
        return self.committed != self.refreshed

    @property
    def diff(self) -> str:
        return "".join(difflib.unified_diff(
            self.committed.splitlines(keepends=True),
            self.refreshed.splitlines(keepends=True),
            fromfile=f"{self.path} (committed)",
            tofile=f"{self.path} (counted)"))


def analyze(values: Mapping[str, str],
            pages: Sequence[Path] = PAGES) -> Result[tuple[PageDrift, ...], PipelineError]:
    """The pages whose committed markers do not hold the counted values."""
    def compare(texts: Sequence[str]) -> Result[tuple[PageDrift, ...], PipelineError]:
        absent = [(page, unfilled(text, values)) for page, text in zip(pages, texts)]
        missing = [(page, names) for page, names in absent if names]
        if missing:
            return Result.err(PipelineError(
                ErrorType.VALIDATION_ERROR,
                "\n".join(f"{page} carries no marker for {', '.join(names)}"
                          for page, names in missing)
                + "\nAdd the <!-- ualib:stat:NAME -->…<!-- /ualib:stat:NAME --> "
                  "pair to the page, or drop the stat from corpus_stats.py."))
        drifts = (PageDrift(page, text, fill(text, values))
                  for page, text in zip(pages, texts))
        return Result.ok(tuple(drift for drift in drifts if drift.stale))

    return sequence_results([read_text(page) for page in pages]).and_then(compare)


# =============================================================================
# The three ways to run it
# =============================================================================

def summary(stats: Stats) -> str:
    """The figures on one line, in the landing page's own words."""
    v = stats.markers
    return (f"{v['modules']} literate modules, {v['loc']} lines of Agda, "
            f"{v['checked']} machine-checked, Agda {v['agda']} · stdlib {v['stdlib']}")


def stale_report(stale: Sequence[PageDrift]) -> PipelineError:
    """The gate's failure message: a unified diff per page, then the one command
    that fixes it."""
    return PipelineError(
        ErrorType.VALIDATION_ERROR,
        "".join(drift.diff for drift in stale)
        + f"\n✗ {len(stale)} page(s) carry stale corpus stats.\n"
          "Run:  make corpus-stats")


def check(src: Path = SRC) -> Result[str, PipelineError]:
    """Verify the committed markers against the tree.  The CI gate."""
    def verdict(stats: Stats) -> Result[str, PipelineError]:
        return analyze(stats.markers).and_then(
            lambda stale: Result.err(stale_report(stale)) if stale
            else Result.ok(f"✓ corpus stats are up to date: {summary(stats)}"))

    return measure_all(src).and_then(verdict)


def refresh(src: Path = SRC) -> Result[str, PipelineError]:
    """Write the counted values into the pages that carry markers."""
    def apply(stats: Stats) -> Result[str, PipelineError]:
        def write(stale: Sequence[PageDrift]) -> Result[str, PipelineError]:
            failed = [w.unwrap_err() for w in
                      [write_text(drift.path, drift.refreshed) for drift in stale]
                      if w.is_err]
            if failed:
                return Result.err(failed[0])
            wrote = ", ".join(str(drift.path) for drift in stale)
            return Result.ok(f"{summary(stats)}\n"
                             + (f"  wrote {wrote}" if stale
                                else "  every page already up to date"))

        return analyze(stats.markers).and_then(write)

    return measure_all(src).and_then(apply)


def emit_json(src: Path = SRC) -> Result[str, PipelineError]:
    """The figures as one JSON record."""
    return measure_all(src).map(lambda stats: json.dumps(stats.record, indent=2))


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Count the landing page's corpus stats; refresh or check them.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true",
                      help="fail (with a diff) if a committed value has drifted")
    mode.add_argument("--json", action="store_true",
                      help="print the figures as one JSON record and exit")
    args = parser.parse_args()

    outcome = emit_json() if args.json else check() if args.check else refresh()

    if outcome.is_err:
        error = outcome.unwrap_err()
        sys.stderr.write(error.message.rstrip("\n") + "\n")
        if error.context:
            sys.stderr.write("  " + ", ".join(f"{k}={v}"
                                              for k, v in error.context.items()) + "\n")
        return 1
    print(outcome.unwrap().rstrip("\n"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
