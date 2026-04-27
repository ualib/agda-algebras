#!/usr/bin/env python3
"""
File: scripts/python/gh_project_render.py

Description:

  Regenerate the issue listings inside docs/GITHUB_PROJECT.md from current
  GitHub state, leaving hand-edited prose untouched.

  The file is treated as a sequence of manual prose segments interleaved
  with regions delimited by HTML-comment markers of the form

      <!-- BEGIN GENERATED: milestone-N -->
      ...
      <!-- END GENERATED: milestone-N -->

  Render preserves manual segments byte-for-byte and rebuilds each
  generated region from the live GitHub API.  The convention is: a region
  with id `milestone-N` is rebuilt from issues whose `milestone-N-*` label
  identifies them as belonging to milestone N, ordered by their `[MN-k]`
  ordinal.  Region ids that don't match this pattern produce a
  no-rendering-rule placeholder so that bad ids fail loudly rather than
  silently emitting nothing.

  This is the steady-state inverse of gh_project_populate.py: populate
  pushes hand-authored markdown to GitHub at bootstrap; render pulls live
  GitHub state back into the same markdown for ongoing maintenance.

Usage:

  python3 gh_project_render.py PATH --repo OWNER/NAME [--check]

  --check          Verify that PATH already matches the rendered output;
                   do not write.  Exits 0 if matches, 1 if differs.
                   Intended for the future CI staleness check (M1-2).
  --no-env-prefix  Don't prefix `gh` with `env -u GH_TOKEN -u GITHUB_TOKEN`.
"""
from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path

# Permit `python3 scripts/python/gh_project_render.py ...` from the repo
# root by ensuring this file's directory is on sys.path before importing
# the sibling private modules.
_SCRIPT_DIR = Path(__file__).resolve().parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))

from _gh_project_lib import GitHubClient, Issue
from _utils import Result, PipelineError, ErrorType
from _utils.file_ops import read_text, write_text


# ── Marker syntax ────────────────────────────────────────────────────────────

BEGIN_RE = re.compile(r"<!--\s*BEGIN GENERATED:\s*([\w-]+)\s*-->")
END_RE   = re.compile(r"<!--\s*END GENERATED:\s*([\w-]+)\s*-->")


@dataclass(frozen=True)
class ParsedFile:
    """A file decomposed into manual prose and named generated regions.

    Invariant: len(manuals) == len(ids) + 1.  The original file is
    reconstructible (modulo regeneration of the marked regions) as

        manuals[0] + <BEGIN ids[0]>...<END ids[0]>
        + manuals[1] + <BEGIN ids[1]>...<END ids[1]>
        + ... + manuals[-1]

    The content between markers in the original file is discarded by parse;
    render rebuilds it from GitHub state.
    """
    manuals: tuple[str, ...]
    ids: tuple[str, ...]


def parse_file(content: str) -> Result[ParsedFile, PipelineError]:
    """Split file content on BEGIN/END GENERATED marker pairs."""
    manuals: list[str] = []
    ids: list[str] = []
    pos = 0
    while True:
        begin = BEGIN_RE.search(content, pos)
        if begin is None:
            manuals.append(content[pos:])
            return Result.ok(ParsedFile(tuple(manuals), tuple(ids)))
        marker_id = begin.group(1)
        manuals.append(content[pos:begin.start()])
        end = END_RE.search(content, begin.end())
        if end is None:
            return Result.err(PipelineError(
                error_type=ErrorType.PARSING_ERROR,
                message=f"unterminated <!-- BEGIN GENERATED: {marker_id} -->",
                context={"offset": begin.start()},
            ))
        if end.group(1) != marker_id:
            return Result.err(PipelineError(
                error_type=ErrorType.PARSING_ERROR,
                message=(
                    f"mismatched markers: BEGIN GENERATED: {marker_id} "
                    f"closed by END GENERATED: {end.group(1)}"
                ),
                context={"begin_offset": begin.start(), "end_offset": end.start()},
            ))
        ids.append(marker_id)
        pos = end.end()


# ── Issue grouping and sorting ───────────────────────────────────────────────

def group_by_milestone(issues: list[Issue]) -> dict[int, list[Issue]]:
    out: dict[int, list[Issue]] = {}
    for issue in issues:
        out.setdefault(issue.milestone_idx, []).append(issue)
    return out


def issue_sort_key(issue: Issue) -> tuple[int, int]:
    m = re.match(r"^M(\d+)-(\d+)$", issue.id)
    return (int(m.group(1)), int(m.group(2))) if m else (10**9, 10**9)


# ── Region rendering ─────────────────────────────────────────────────────────

_ID_PREFIX_RE = re.compile(r"^\[M\d+-\d+\]\s+(.+)$")


def strip_id_prefix(title: str) -> str:
    """Drop the leading `[MN-k]` from an issue title; the heading reproduces
    the identifier separately, so leaving it in the title text is redundant."""
    m = _ID_PREFIX_RE.match(title)
    return m.group(1) if m else title


def render_issue(issue: Issue) -> str:
    title = strip_id_prefix(issue.title)
    state_suffix = ", closed" if issue.state == "closed" else ""
    ref = f"#{issue.gh_number}{state_suffix}" if issue.gh_number else "(no number)"
    labels = ", ".join(f"`{lbl}`" for lbl in issue.labels)
    body = issue.body.strip() if issue.body else "_(no description on GitHub)_"
    return (
        f"### Issue {issue.id}: {title} ({ref})\n"
        f"\n"
        f"**Labels**: {labels}\n"
        f"\n"
        f"{body}\n"
    )


def render_region(region_id: str, issues_by_ms: dict[int, list[Issue]]) -> str:
    m = re.match(r"^milestone-(\d+)$", region_id)
    if m is None:
        return f"\n<!-- region '{region_id}' has no rendering rule in gh_project_render.py -->\n"
    n = int(m.group(1))
    issues = issues_by_ms.get(n, [])
    if not issues:
        return f"\n_(no open or closed issues with `milestone-{n}-*` label)_\n"
    blocks = [render_issue(i) for i in sorted(issues, key=issue_sort_key)]
    return "\n" + "\n---\n\n".join(blocks) + "\n"


def assemble_file(parsed: ParsedFile, issues_by_ms: dict[int, list[Issue]]) -> str:
    parts: list[str] = []
    for i, manual in enumerate(parsed.manuals[:-1]):
        rid = parsed.ids[i]
        parts.append(manual)
        parts.append(f"<!-- BEGIN GENERATED: {rid} -->\n")
        parts.append(render_region(rid, issues_by_ms))
        parts.append(f"<!-- END GENERATED: {rid} -->")
    parts.append(parsed.manuals[-1])
    return "".join(parts)


# ── Validation ───────────────────────────────────────────────────────────────

def warn_orphan_milestones(parsed: ParsedFile, issues_by_ms: dict[int, list[Issue]]) -> None:
    """Stderr-warn for each milestone-N-* label group lacking a marker
    region in the file.  Such issues are silently dropped from output;
    surfacing the warning lets the maintainer notice and add the region."""
    region_milestones: set[int] = set()
    for rid in parsed.ids:
        m = re.match(r"^milestone-(\d+)$", rid)
        if m is not None:
            region_milestones.add(int(m.group(1)))
    for n, issues in sorted(issues_by_ms.items()):
        if n not in region_milestones:
            print(
                f"warning: {len(issues)} issue(s) with milestone-{n}-* label "
                f"have no <!-- BEGIN GENERATED: milestone-{n} --> region",
                file=sys.stderr,
            )


# ── Main ─────────────────────────────────────────────────────────────────────

def _render(parsed: ParsedFile, issues: list[Issue]) -> str:
    issues_by_ms = group_by_milestone(issues)
    warn_orphan_milestones(parsed, issues_by_ms)
    return assemble_file(parsed, issues_by_ms)


def run(args: argparse.Namespace) -> Result[str, PipelineError]:
    """Pure-ish core: returns the rendered file content."""
    client = GitHubClient(
        repo=args.repo,
        dry_run=False,
        env_prefix=not args.no_env_prefix,
    )
    return (
        read_text(args.markdown)
        .and_then(parse_file)
        .and_then(lambda parsed:
            client.list_issues().map(lambda issues: _render(parsed, issues))
        )
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Regenerate generated regions of GITHUB_PROJECT.md from GitHub.",
    )
    parser.add_argument("markdown", type=Path, help="Path to GITHUB_PROJECT.md.")
    parser.add_argument("--repo", required=True, help="GitHub repo (OWNER/NAME).")
    parser.add_argument(
        "--check",
        action="store_true",
        help="Verify that PATH already matches the rendered output; do not write.",
    )
    parser.add_argument(
        "--no-env-prefix",
        action="store_true",
        help="Don't prefix `gh` with `env -u GH_TOKEN -u GITHUB_TOKEN`.",
    )
    args = parser.parse_args()

    result = run(args)
    if result.is_err:
        print(f"render failed: {result.unwrap_err()}", file=sys.stderr)
        return 1
    rendered = result.unwrap()

    if args.check:
        existing = args.markdown.read_text(encoding="utf-8")
        if existing == rendered:
            print(f"OK: {args.markdown} matches rendered output")
            return 0
        print(f"FAIL: {args.markdown} differs from rendered output", file=sys.stderr)
        print("       (run without --check to update in place)", file=sys.stderr)
        return 1

    write_result = write_text(args.markdown, rendered)
    if write_result.is_err:
        print(f"write failed: {write_result.unwrap_err()}", file=sys.stderr)
        return 1
    print(f"wrote {args.markdown}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
