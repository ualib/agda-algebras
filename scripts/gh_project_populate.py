#!/usr/bin/env python3
"""
gh_project_populate.py

File: scripts/gh_project_populate.py

Description:

  Create GitHub milestones, labels, and issues from a structured Markdown project plan.

Usage:
    python gh_project_populate.py PROJECT_PLAN.md --repo OWNER/REPO [OPTIONS]

The script parses the markdown file produced by the agda-native-air project
planning process and creates:
  1. Labels (idempotent — skips existing)
  2. Milestones (idempotent — skips existing, returns milestone numbers)
  3. Issues (with milestone and label assignments)

Requirements:
  - Python 3.8+
  - `gh` CLI installed and authenticated
  - Repository must already exist on GitHub

Options:
  --dry-run          Print what would be created without making API calls
  --milestones-only  Only create milestones (skip labels and issues)
  --labels-only      Only create labels
  --issues-only      Only create issues (milestones and labels must exist)
  --skip-labels      Skip label creation
  --start-from ID    Start issue creation from this issue ID (e.g., M1-3)
  --env-prefix       Prefix gh commands with `env -u GH_TOKEN -u GITHUB_TOKEN`
                     to work around token precedence issues (default: True)
  --no-env-prefix    Disable the env prefix
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import textwrap
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional


# ── Data classes ──────────────────────────────────────────────────────────────

@dataclass
class Label:
    name: str
    color: str
    description: str = ""


@dataclass
class Milestone:
    number: int  # 0-based index from the markdown (M0, M1, ...)
    title: str
    description: str
    gh_number: Optional[int] = None  # GitHub-assigned milestone number


@dataclass
class Issue:
    id: str          # e.g. "M0-1"
    title: str
    body: str
    labels: list[str] = field(default_factory=list)
    milestone_idx: int = 0  # which milestone (0, 1, 2, ...)


# ── Markdown parser ──────────────────────────────────────────────────────────

def parse_project_plan(md_path: Path) -> tuple[list[Milestone], list[Label], list[Issue]]:
    """Parse the structured project plan markdown into milestones, labels, and issues."""

    text = md_path.read_text(encoding="utf-8")

    milestones = _parse_milestones(text)
    labels = _parse_labels(text)
    issues = _parse_issues(text)

    return milestones, labels, issues


def _parse_milestones(text: str) -> list[Milestone]:
    """Extract milestones from the ## Milestones section."""
    milestones = []

    # Find the Milestones section
    ms_match = re.search(r"^## Milestones\s*$", text, re.MULTILINE)
    if not ms_match:
        return milestones

    ms_text = text[ms_match.end():]
    # Stop at the next ## that isn't ### (i.e., next top-level section)
    next_section = re.search(r"^## (?!#)", ms_text, re.MULTILINE)
    if next_section:
        ms_text = ms_text[:next_section.start()]

    # Each milestone starts with ### Milestone N —
    ms_blocks = re.split(r"^### Milestone (\d+) — (.+)$", ms_text, flags=re.MULTILINE)

    # ms_blocks[0] is preamble, then groups of (number, title, body)
    i = 1
    while i + 2 < len(ms_blocks):
        num = int(ms_blocks[i])
        title = ms_blocks[i + 1].strip()
        body = ms_blocks[i + 2].strip()

        # Extract description (text between **Description:** and **Exit criterion:**)
        desc_match = re.search(
            r"\*\*Description[:\*]*\*?\s*\n(.*?)(?=\*\*Exit criterion|---|\Z)",
            body, re.DOTALL
        )
        desc = desc_match.group(1).strip() if desc_match else ""

        # Extract exit criterion
        exit_match = re.search(
            r"\*\*Exit criterion[:\*]*\*?\s*(.+?)(?=\n---|\n\n###|\Z)",
            body, re.DOTALL
        )
        exit_crit = exit_match.group(1).strip() if exit_match else ""

        full_desc = desc
        if exit_crit:
            full_desc += f"\n\n**Exit criterion:** {exit_crit}"

        milestones.append(Milestone(
            number=num,
            title=f"{num}. {title}",
            description=full_desc,
        ))
        i += 3

    return milestones


def _parse_labels(text: str) -> list[Label]:
    """Collect labels from the markdown.

    Preferred: an explicit ``## Labels`` section with entries of the form

        - `label-name` (COLORHEX) — Description

    (The separator may be em-dash, en-dash, hyphen, or colon.)

    Fallback 1: if no ``## Labels`` section is present, collect all label
    names referenced in issues' ``**Labels:**`` lines and give them a
    neutral gray color with no description.  This implements the
    "create a new label whenever we encounter one we don't recognize"
    policy.

    Fallback 2: if there are no issues with ``**Labels:**`` lines either,
    return a small project-agnostic default set so the script still works
    out of the box.
    """
    # 1) Try to parse an explicit ## Labels section.
    explicit = _parse_explicit_labels(text)
    if explicit:
        return explicit

    # 2) Fallback: collect label names from issue references.
    collected = _collect_labels_from_issues(text)
    if collected:
        return collected

    # 3) Last resort: minimal project-agnostic defaults.
    return [
        Label("good first issue", "7057ff", "Good for newcomers"),
        Label("documentation",    "0e8a16", "Documentation"),
        Label("help-wanted",      "0e8a16", "Community help wanted"),
    ]


def _parse_explicit_labels(text: str) -> list[Label]:
    """Parse the ``## Labels`` section into Label records, if it exists."""
    m = re.search(r"^## Labels\s*$", text, re.MULTILINE)
    if not m:
        return []
    start = m.end()
    next_section = re.search(r"^## (?!#)", text[start:], re.MULTILINE)
    end = start + next_section.start() if next_section else len(text)
    section = text[start:end]
    pattern = re.compile(
        r"^\s*[-*]\s+`([^`]+)`\s*\(([0-9a-fA-F]{6})\)\s*(?:—|–|-|:)\s*(.+?)\s*$",
        re.MULTILINE,
    )
    return [
        Label(mm.group(1).strip(), mm.group(2).strip().lower(), mm.group(3).strip())
        for mm in pattern.finditer(section)
    ]


def _collect_labels_from_issues(text: str) -> list[Label]:
    """Collect unique label names referenced in issues' ``**Labels:**`` lines."""
    seen: dict[str, Label] = {}
    for m in re.finditer(r"\*\*Labels:\*\*\s*(.+)", text):
        for raw in m.group(1).split(","):
            name = raw.strip().strip("`").strip()
            if name and name not in seen:
                seen[name] = Label(name, "cccccc", "")
    return list(seen.values())


def _parse_issues(text: str) -> list[Issue]:
    """Extract issues from the ## Issues / ## Milestone N sections."""
    issues = []

    # Split on issue headers: ### Issue M{n}-{m}: Title
    issue_pattern = re.compile(
        r"^### Issue (M\d+-\d+): (.+?)$",
        re.MULTILINE,
    )

    matches = list(issue_pattern.finditer(text))

    for idx, match in enumerate(matches):
        issue_id = match.group(1)
        title = match.group(2).strip()

        # Extract milestone index from ID
        ms_idx = int(re.match(r"M(\d+)", issue_id).group(1))

        # Body runs from after the header to the next issue header
        start = match.end()
        if idx + 1 < len(matches):
            end = matches[idx + 1].start()
        else:
            # Stop at the summary section
            summary_match = re.search(r"^## Summary:", text[start:], re.MULTILINE)
            end = start + summary_match.start() if summary_match else len(text)

        raw_body = text[start:end].strip()

        # Truncate at milestone section headers that leaked in
        # (happens for the last issue in each milestone section)
        ms_leak = re.search(r"\n---+\s*\n+## Milestone \d+", raw_body)
        if ms_leak:
            raw_body = raw_body[:ms_leak.start()].strip()

        # Remove trailing --- separators
        raw_body = re.sub(r"\n---+\s*$", "", raw_body).strip()

        # Extract labels from the **Labels:** line
        labels_match = re.search(r"\*\*Labels:\*\*\s*(.+)", raw_body)
        labels = []
        if labels_match:
            label_str = labels_match.group(1).strip()
            labels = [l.strip().strip("`") for l in label_str.split(",")]

        # Extract milestone line
        ms_line_match = re.search(r"\*\*Milestone:\*\*\s*(.+)", raw_body)

        # Build the issue body: remove the Labels and Milestone metadata lines
        body_lines = []
        for line in raw_body.split("\n"):
            if line.strip().startswith("**Labels:**"):
                continue
            if line.strip().startswith("**Milestone:**"):
                continue
            body_lines.append(line)

        body = "\n".join(body_lines).strip()

        # Clean up leading blank lines
        body = re.sub(r"^\n+", "", body)

        issues.append(Issue(
            id=issue_id,
            title=title,
            body=body,
            labels=labels,
            milestone_idx=ms_idx,
        ))

    return issues


# ── GitHub API calls ─────────────────────────────────────────────────────────

class GitHubClient:
    """Thin wrapper around `gh` CLI."""

    def __init__(self, repo: str, dry_run: bool = False, env_prefix: bool = True):
        self.repo = repo
        self.dry_run = dry_run
        self.env_prefix = env_prefix
        self._milestone_cache: dict[str, int] = {}  # title → gh number

    def _gh_cmd(self, *args: str) -> list[str]:
        """Build the gh command, optionally with env prefix."""
        cmd = []
        if self.env_prefix:
            cmd = ["env", "-u", "GH_TOKEN", "-u", "GITHUB_TOKEN"]
        cmd.extend(["gh"])
        cmd.extend(args)
        return cmd

    def _run(self, cmd: list[str], check: bool = True) -> subprocess.CompletedProcess:
        """Run a command and return the result."""
        if self.dry_run:
            print(f"  [DRY RUN] {' '.join(cmd)}")
            return subprocess.CompletedProcess(cmd, 0, stdout=b'{"number": 0}', stderr=b'')

        result = subprocess.run(
            cmd,
            capture_output=True,
            text=False,  # get bytes
        )

        if check and result.returncode != 0:
            stderr = result.stderr.decode("utf-8", errors="replace")
            # Don't fail on "already exists" errors
            if "already exists" in stderr.lower():
                print(f"    (already exists, skipping)")
                return result
            print(f"  ⚠ Command failed (exit {result.returncode}):")
            print(f"    stderr: {stderr[:500]}")
            return result

        return result

    # ── Labels ────────────────────────────────────────────────────────────

    def create_label(self, label: Label) -> bool:
        """Create a label. Returns True if created, False if it already existed."""
        print(f"  Creating label: {label.name} (#{label.color})")

        cmd = self._gh_cmd(
            "label", "create", label.name,
            "--color", label.color,
            "--repo", self.repo,
        )
        if label.description:
            cmd.extend(["--description", label.description])

        result = self._run(cmd, check=False)
        return result.returncode == 0

    # ── Milestones ────────────────────────────────────────────────────────

    def get_existing_milestones(self) -> dict[str, int]:
        """Fetch existing milestones and return {title: number}."""
        if self.dry_run:
            return {}

        cmd = self._gh_cmd(
            "api", f"repos/{self.repo}/milestones",
            "--method", "GET",
            "-f", "state=all",
            "-f", "per_page=100",
        )
        result = self._run(cmd, check=False)
        if result.returncode != 0:
            return {}

        try:
            data = json.loads(result.stdout)
            return {m["title"]: m["number"] for m in data}
        except (json.JSONDecodeError, KeyError):
            return {}

    def create_milestone(self, milestone: Milestone) -> Optional[int]:
        """Create a milestone. Returns the GitHub milestone number."""
        existing = self._milestone_cache or self.get_existing_milestones()
        self._milestone_cache = existing

        if milestone.title in existing:
            gh_num = existing[milestone.title]
            print(f"  Milestone '{milestone.title}' already exists (#{gh_num})")
            return gh_num

        print(f"  Creating milestone: {milestone.title}")

        cmd = self._gh_cmd(
            "api", f"repos/{self.repo}/milestones",
            "--method", "POST",
            "-f", f"title={milestone.title}",
            "-f", f"description={milestone.description}",
            "-f", "state=open",
        )

        result = self._run(cmd)
        if self.dry_run:
            return 0

        try:
            data = json.loads(result.stdout)
            gh_num = data.get("number", 0)
            self._milestone_cache[milestone.title] = gh_num
            print(f"    → milestone #{gh_num}")
            return gh_num
        except (json.JSONDecodeError, KeyError):
            print(f"    ⚠ Could not parse milestone response")
            return None

    # ── Issues ────────────────────────────────────────────────────────────

    def create_issue(self, issue: Issue, milestone_title: Optional[str] = None) -> Optional[int]:
        """Create an issue. Returns the GitHub issue number.

        Note: `gh issue create --milestone` expects the milestone TITLE (a string),
        not the GitHub API milestone number.
        """
        # Build the title with the issue ID prefix
        full_title = f"[{issue.id}] {issue.title}"
        print(f"  Creating issue: {full_title}")

        cmd = self._gh_cmd(
            "issue", "create",
            "--repo", self.repo,
            "--title", full_title,
            "--body", issue.body,
        )

        # Add labels
        for label in issue.labels:
            cmd.extend(["--label", label])

        # Add milestone (gh issue create expects the title, not the number)
        if milestone_title:
            cmd.extend(["--milestone", milestone_title])

        result = self._run(cmd)

        if self.dry_run:
            return 0

        # gh issue create prints the URL on success
        stdout = result.stdout.decode("utf-8", errors="replace").strip()
        if stdout:
            # Extract issue number from URL
            num_match = re.search(r"/issues/(\d+)", stdout)
            if num_match:
                gh_num = int(num_match.group(1))
                print(f"    → issue #{gh_num}: {stdout}")
                return gh_num
            else:
                print(f"    → {stdout}")
        return None


# ── Main logic ───────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="Populate a GitHub project from a structured Markdown plan.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=textwrap.dedent("""\
            Examples:
              # Dry run — see what would be created:
              python gh_project_populate.py plan.md --repo owner/repo --dry-run

              # Create everything:
              python gh_project_populate.py plan.md --repo owner/repo

              # Only milestones:
              python gh_project_populate.py plan.md --repo owner/repo --milestones-only

              # Resume from a specific issue:
              python gh_project_populate.py plan.md --repo owner/repo --issues-only --start-from M1-3
        """),
    )
    parser.add_argument("markdown", type=Path, help="Path to the project plan markdown file")
    parser.add_argument("--repo", required=True, help="GitHub repo (owner/name)")
    parser.add_argument("--dry-run", action="store_true", help="Print commands without executing")
    parser.add_argument("--milestones-only", action="store_true")
    parser.add_argument("--labels-only", action="store_true")
    parser.add_argument("--issues-only", action="store_true")
    parser.add_argument("--skip-labels", action="store_true")
    parser.add_argument("--start-from", type=str, default=None,
                        help="Start issue creation from this ID (e.g., M1-3)")
    parser.add_argument("--env-prefix", action="store_true", default=True,
                        help="Prefix gh with `env -u GH_TOKEN -u GITHUB_TOKEN` (default)")
    parser.add_argument("--no-env-prefix", action="store_true",
                        help="Don't prefix gh commands with env")
    parser.add_argument("--delay", type=float, default=1.5,
                        help="Seconds to wait between API calls (default: 1.5)")

    args = parser.parse_args()

    if args.no_env_prefix:
        args.env_prefix = False

    if not args.markdown.exists():
        print(f"Error: {args.markdown} not found", file=sys.stderr)
        sys.exit(1)

    # ── Parse ─────────────────────────────────────────────────────────────
    print(f"Parsing {args.markdown}...")
    milestones, labels, issues = parse_project_plan(args.markdown)

    print(f"  Found {len(milestones)} milestones, {len(labels)} labels, {len(issues)} issues")
    print()

    # ── Confirmation ──────────────────────────────────────────────────────
    if not args.dry_run:
        print(f"Target repo: {args.repo}")
        print(f"Env prefix:  {'yes' if args.env_prefix else 'no'}")
        print()

        what = []
        if not args.issues_only and not args.labels_only:
            what.append(f"{len(milestones)} milestones")
        if not args.issues_only and not args.milestones_only and not args.skip_labels:
            what.append(f"{len(labels)} labels")
        if not args.milestones_only and not args.labels_only:
            count = len(issues)
            if args.start_from:
                count = len([i for i in issues if _issue_id_gte(i.id, args.start_from)])
            what.append(f"{count} issues")

        print(f"This will create: {', '.join(what)}")
        response = input("Continue? [y/N] ").strip().lower()
        if response not in ("y", "yes"):
            print("Aborted.")
            sys.exit(0)
        print()

    # ── Client ────────────────────────────────────────────────────────────
    gh = GitHubClient(repo=args.repo, dry_run=args.dry_run, env_prefix=args.env_prefix)

    # ── Labels ────────────────────────────────────────────────────────────
    if not args.issues_only and not args.milestones_only and not args.skip_labels:
        print("═" * 60)
        print("CREATING LABELS")
        print("═" * 60)
        for label in labels:
            gh.create_label(label)
            if not args.dry_run:
                time.sleep(0.5)
        print()

    if args.labels_only:
        print("Done (labels only).")
        return

    # ── Milestones ────────────────────────────────────────────────────────
    ms_title_map: dict[int, str] = {}  # milestone_idx → milestone title (for gh issue create)

    if not args.issues_only:
        print("═" * 60)
        print("CREATING MILESTONES")
        print("═" * 60)
        for ms in milestones:
            gh_num = gh.create_milestone(ms)
            if gh_num is not None:
                ms_title_map[ms.number] = ms.title
                ms.gh_number = gh_num
            if not args.dry_run:
                time.sleep(args.delay)
        print()
    else:
        # Need to fetch existing milestones to verify they exist
        print("Fetching existing milestones...")
        existing = gh.get_existing_milestones()
        for ms in milestones:
            if ms.title in existing:
                ms_title_map[ms.number] = ms.title
                ms.gh_number = existing[ms.title]
        print(f"  Found {len(ms_title_map)} existing milestones")
        for idx, title in sorted(ms_title_map.items()):
            print(f"    M{idx} → \"{title}\"")
        print()

    if args.milestones_only:
        print("Done (milestones only).")
        return

    # ── Issues ────────────────────────────────────────────────────────────
    print("═" * 60)
    print("CREATING ISSUES")
    print("═" * 60)

    skipping = args.start_from is not None
    created = 0
    failed = 0

    for issue in issues:
        # Handle --start-from
        if skipping:
            if issue.id == args.start_from:
                skipping = False
            else:
                print(f"  Skipping {issue.id} (before --start-from {args.start_from})")
                continue

        ms_title = ms_title_map.get(issue.milestone_idx)
        result = gh.create_issue(issue, milestone_title=ms_title)

        if result is not None:
            created += 1
        else:
            failed += 1

        if not args.dry_run:
            time.sleep(args.delay)

    print()
    print("═" * 60)
    print(f"DONE: {created} issues created, {failed} failed")
    print("═" * 60)


def _issue_id_gte(a: str, b: str) -> bool:
    """Compare issue IDs like M0-1 >= M1-3."""
    def parse(s):
        m = re.match(r"M(\d+)-(\d+)", s)
        return (int(m.group(1)), int(m.group(2))) if m else (999, 999)
    return parse(a) >= parse(b)


if __name__ == "__main__":
    main()
