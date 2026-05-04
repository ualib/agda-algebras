"""
File: scripts/python/_gh_project_lib.py

Description:

  Shared data model and GitHub I/O layer for the gh_project_{populate, render}
  scripts.  Provides the Label / Milestone / Issue records, a thin GitHubClient
  wrapping the `gh` CLI with both write-side methods (used by populate) and
  read-side methods (used by render), and helpers for parsing the [MN-k] issue
  identifiers that anchor cross-script behavior.

  Both scripts speak the same domain vocabulary; centralizing it here makes the
  populate/render symmetry visible in the directory listing and prevents the
  two scripts from drifting on conventions that ought to be shared (label
  colors, milestone-N-* label semantics, the `env -u GH_TOKEN -u GITHUB_TOKEN`
  workaround for token-precedence bugs in `gh`, etc.).

  All GitHubClient methods return Result[T, PipelineError] for functional
  composition by callers; populate consumes these by unwrapping at the call
  site to preserve its existing imperative shape, while render is built
  Result-native end to end.

Provenance:

  Extracted from scripts/python/gh_project_populate.py during the work for
  agda-algebras issue #289.  Originally adapted from
  formalverification/agda-native-air.
"""
from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from typing import Optional

from _utils import Result, PipelineError, ErrorType
from _utils.command_runner import run_command


# ── Issue identifier conventions ────────────────────────────────────────────

# Issue titles are prefixed with `[MN-k]` (or `[MN-k{a..z}]` for sub-tickets
# of a fan-out parent) for cross-script identification and within-milestone
# ordering.  Examples: `[M0-1] ...`, `[M1-12] ...`, `[M2-7a] ...`.
ISSUE_ID_PATTERN = re.compile(r"^\[(M(\d+)-(\d+)([a-z]?))\]\s+(.+)$")

# Labels of the form `milestone-N-*` map issues to milestone N.  Populate
# emits these labels; render uses them to infer milestone membership when
# pulling state back from GitHub.
MILESTONE_LABEL_PATTERN = re.compile(r"^milestone-(\d+)-")


def parse_issue_id(title: str) -> Optional[tuple[str, int, int, str, str]]:
    """Parse a `[MN-k] Title` prefix into (id, milestone, ordinal, suffix, rest).

    Returns None if the title does not begin with a recognized prefix.
    Used by populate's idempotency guard and by render's title-based ordering.
    The suffix is "" for plain `[MN-k]` ids and a single lowercase letter for
    fan-out sub-tickets like `[M2-7a]`, `[M2-7b]`.
    """
    m = ISSUE_ID_PATTERN.match(title)
    if not m:
        return None
    issue_id = m.group(1)
    ms = int(m.group(2))
    ord_ = int(m.group(3))
    suffix = m.group(4) or ""
    rest = m.group(5)
    return issue_id, ms, ord_, suffix, rest


def milestone_index_from_labels(labels: list[str]) -> Optional[int]:
    """Infer milestone number from a `milestone-N-*` label, or None if absent."""
    for label in labels:
        m = MILESTONE_LABEL_PATTERN.match(label)
        if m:
            return int(m.group(1))
    return None


def issue_id_gte(a: str, b: str) -> bool:
    """Compare issue IDs lexicographically by (milestone, ordinal).

    Compare by (milestone, ordinal, suffix).  `M1-3 >= M1-2` is True;
    `M0-9 >= M1-1` is False; `M2-7a >= M2-7` is True; `M2-7b >= M2-7a` is True.
    Used by populate's --start-from logic and by render to order issues
    within a milestone.
    """
    def parse(s: str) -> tuple[int, int, str]:
        m = re.match(r"M(\d+)-(\d+)([a-z]?)", s)
        return (int(m.group(1)), int(m.group(2)), m.group(3) or "") if m else (10**9, 10**9, "")
    return parse(a) >= parse(b)


# ── Data classes ────────────────────────────────────────────────────────────

@dataclass(frozen=True)
class Label:
    """A GitHub label with its display color and optional description."""
    name: str
    color: str          # six hex digits, no leading `#`
    description: str = ""


@dataclass(frozen=True)
class Milestone:
    """A GitHub milestone; `gh_number` is set after creation or lookup."""
    number: int                        # 1-based plan index, matching the
                                       # leading integer of the GitHub title
                                       # ("1. Infrastructure health" → 1)
    title: str                         # GitHub display title, e.g. "1. Infrastructure"
    description: str
    gh_number: Optional[int] = None    # GitHub-assigned milestone number

    def with_gh_number(self, n: int) -> Milestone:
        """Return a copy with `gh_number` populated (immutable update)."""
        return Milestone(self.number, self.title, self.description, n)


@dataclass(frozen=True)
class Issue:
    """A GitHub issue carrying the full information needed by both scripts."""
    id: str                                   # e.g. "M0-1"; parsed from title prefix
    title: str                                # full title including `[MN-k]` prefix
    body: str
    labels: tuple[str, ...] = ()
    milestone_idx: int = 0                    # 1-based plan index, matching the
                                              # `milestone-N-*` label group; default 0
                                              # means "unclassified" (no matching label)
    state: str = "open"                       # "open" or "closed"; render-only
    gh_number: Optional[int] = None           # GitHub-assigned issue number; render-only


# ── GitHub client ────────────────────────────────────────────────────────────

@dataclass(frozen=True)
class GitHubClient:
    """Thin Result-returning wrapper around the `gh` CLI.

    Idempotent on labels and milestones (existing entities are detected and
    skipped on the write path).  Read-side methods (`list_*`) provide the
    state-pull half of the populate/render symmetry.

    Dry-run contract: when `dry_run=True`, no write API calls are made, but
    read calls (`list_*`) still occur — they're needed to make idempotency
    visible in the dry-run output.  An entity that already exists is
    reported as `- exists: ...`; a genuinely-new entity is reported as
    `[dry-run] would create ...`.  Running --dry-run against an
    already-populated repo therefore produces a clean inventory rather
    than the misleading "would create everything" output of an earlier
    iteration of this client.

    The `env_prefix` flag prepends `env -u GH_TOKEN -u GITHUB_TOKEN` to every
    invocation, working around a long-standing `gh` quirk where these
    environment variables silently override the keychain-stored auth token
    even when both are present.  Default-on is the safer choice; pass
    `env_prefix=False` only if the calling environment is known to have those
    variables already unset.
    """
    repo: str
    dry_run: bool = False
    env_prefix: bool = True

    # — internal command construction ——————————————————————————————————

    def _gh(self, *args: str) -> list[str]:
        prefix = ["env", "-u", "GH_TOKEN", "-u", "GITHUB_TOKEN"] if self.env_prefix else []
        return prefix + ["gh", *args]

    def _run(self, *args: str) -> Result[str, PipelineError]:
        """Run `gh ...` and return stdout as text on success."""
        return run_command(self._gh(*args), capture_output=True, text=True).map(
            lambda proc: proc.stdout
        )

    # — labels ——————————————————————————————————————————————————————————

    def list_labels(self) -> Result[list[Label], PipelineError]:
        """Pull every label currently defined on the repository."""
        cmd = self._run(
            "label", "list", "--repo", self.repo, "--limit", "200",
            "--json", "name,color,description",
        )
        return cmd.and_then(_parse_labels_json)

    def create_label(self, label: Label) -> Result[tuple[str, bool], PipelineError]:
        """Create `label` on GitHub.  Returns (name, was_created), where
        was_created is True if a new label was created on this call and
        False if an identically-named label already existed.  Idempotent."""
        return self.list_labels().and_then(
            lambda existing: _find_or_create_label(self, label, existing)
        )

    # — milestones ——————————————————————————————————————————————————————

    def list_milestones(self) -> Result[list[Milestone], PipelineError]:
        """Pull every milestone (open and closed) from the repository.

        The GitHub CLI lacks first-class milestone subcommands, so we go
        through the REST API.  Returned `Milestone.number` is zero-based to
        match the plan's M0/M1/M2 indexing; `gh_number` carries GitHub's
        own number for cross-reference.
        """
        cmd = self._run(
            "api", f"repos/{self.repo}/milestones",
            "--paginate",
            "-X", "GET",
            "-F", "state=all",
            "-F", "per_page=100",
        )
        return cmd.and_then(_parse_milestones_json)

    def create_milestone(
        self, ms: Milestone
    ) -> Result[tuple[Milestone, bool], PipelineError]:
        """Create `ms` on GitHub.  Returns (milestone, was_created), where
        the milestone has its gh_number populated and was_created is True
        if a new milestone was created on this call and False if an
        existing milestone with the same title was reused.  Idempotent."""
        return self.list_milestones().and_then(
            lambda existing: _find_or_create_milestone(self, ms, existing)
        )

    # — issues ——————————————————————————————————————————————————————————

    def list_issues(self) -> Result[list[Issue], PipelineError]:
        """Pull every issue (open and closed) from the repository.

        Returned `Issue.milestone_idx` is inferred from the issue's
        `milestone-N-*` label rather than from GitHub's milestone assignment;
        the label is the source of truth in this project's convention because
        it survives milestone renames.
        """
        cmd = self._run(
            "issue", "list",
            "--repo", self.repo,
            "--state", "all",
            "--limit", "1000",
            "--json", "number,title,body,labels,milestone,state",
        )
        return cmd.and_then(_parse_issues_json)

    def create_issue(
        self, issue: Issue, milestone_title: Optional[str]
    ) -> Result[tuple[int, bool], PipelineError]:
        """Create `issue` on GitHub.  Returns (gh_number, was_created), where
        was_created is True if a new issue was created on this call and
        False if an existing issue with the same `[MN-k]` prefix was found.
        Idempotent."""
        return self.list_issues().and_then(
            lambda existing: _find_or_create_issue(self, issue, milestone_title, existing)
        )


# ── JSON parsers ─────────────────────────────────────────────────────────────
#
# Pulled out as module-level pure functions to keep GitHubClient methods short
# and to make each parser independently testable.  Each returns Result so the
# pipeline composes through `and_then` without intermediate try/except blocks.

def _parse_labels_json(stdout: str) -> Result[list[Label], PipelineError]:
    return _parse_json(stdout, "labels").map(
        lambda data: [
            Label(
                name=item["name"],
                color=item.get("color", "cccccc"),
                description=item.get("description", "") or "",
            )
            for item in data
        ]
    )


def _parse_milestones_json(stdout: str) -> Result[list[Milestone], PipelineError]:
    """Convert the GitHub REST `repos/.../milestones` response into Milestones.

    The API titles each milestone as e.g. `1. Infrastructure health`; we use
    the leading integer as the zero-based plan index.  Milestones whose title
    does not match this convention are skipped (with no error) since they
    were not created by this tooling and do not belong in the plan.
    """
    title_pattern = re.compile(r"^(\d+)\.\s+(.+)$")
    def to_milestones(data: list[dict]) -> list[Milestone]:
        out: list[Milestone] = []
        for item in data:
            m = title_pattern.match(item.get("title", ""))
            if not m:
                continue
            idx = int(m.group(1))
            out.append(Milestone(
                number=idx,
                title=item["title"],
                description=item.get("description") or "",
                gh_number=item["number"],
            ))
        return sorted(out, key=lambda x: x.number)
    return _parse_json(stdout, "milestones").map(to_milestones)


def _parse_issues_json(stdout: str) -> Result[list[Issue], PipelineError]:
    def to_issues(data: list[dict]) -> list[Issue]:
        out: list[Issue] = []
        for item in data:
            title = item.get("title", "")
            parsed = parse_issue_id(title)
            if parsed is None:
                # Not a planning issue (e.g. an ad-hoc bug report).  Skip
                # silently; render does not list these.
                continue
            issue_id, ms_idx, _ord, _suffix, _rest = parsed
            label_names = tuple(lbl["name"] for lbl in item.get("labels", []) or [])
            # Prefer the milestone-N-* label; fall back to the leading integer
            # of GitHub's milestone title.  The label is canonical because it
            # survives milestone-title edits.
            inferred = milestone_index_from_labels(list(label_names))
            if inferred is None:
                gh_ms = item.get("milestone") or {}
                gh_title = gh_ms.get("title", "")
                tm = re.match(r"^(\d+)\.", gh_title)
                inferred = int(tm.group(1)) if tm else ms_idx
            out.append(Issue(
                id=issue_id,
                title=title,
                body=item.get("body") or "",
                labels=label_names,
                milestone_idx=inferred,
                state=item.get("state", "open").lower(),
                gh_number=item.get("number"),
            ))
        return out
    return _parse_json(stdout, "issues").map(to_issues)


def _parse_json(stdout: str, kind: str) -> Result[list[dict], PipelineError]:
    """Decode the JSON body of a `gh` invocation, with structured errors."""
    try:
        data = json.loads(stdout)
    except json.JSONDecodeError as e:
        return Result.err(PipelineError(
            error_type=ErrorType.PARSING_ERROR,
            message=f"failed to decode {kind} JSON from `gh`",
            cause=e,
            context={"stdout_preview": stdout[:500]},
        ))
    if not isinstance(data, list):
        return Result.err(PipelineError(
            error_type=ErrorType.PARSING_ERROR,
            message=f"expected a JSON list of {kind}, got {type(data).__name__}",
        ))
    return Result.ok(data)


# ── Idempotent-create helpers ────────────────────────────────────────────────
#
# Kept as module-level closures (rather than methods on GitHubClient) to keep
# the client's surface compact and to make the pure decision logic separately
# testable from the I/O.
#
# Each helper receives the current state of the corresponding GitHub entity
# (already fetched by the caller) and decides between three outcomes: report
# the entity as existing and return its ID, preview the creation under
# dry_run, or perform the real create.  Keeping the existence check ahead of
# the dry-run branch means dry-run output accurately reflects what will
# happen during a live run.

def _find_or_create_label(
    client: GitHubClient,
    label: Label,
    existing: list[Label],
) -> Result[tuple[str, bool], PipelineError]:
    if any(e.name == label.name for e in existing):
        print(f"  - exists: label {label.name}")
        return Result.ok((label.name, False))
    if client.dry_run:
        print(f"  [dry-run] would create label: {label.name} (#{label.color})")
        return Result.ok((label.name, True))
    return client._run(
        "label", "create", label.name,
        "--repo", client.repo,
        "--color", label.color,
        "--description", label.description,
    ).map(lambda _: (label.name, True))

def _find_or_create_milestone(
    client: GitHubClient,
    ms: Milestone,
    existing: list[Milestone],
) -> Result[tuple[Milestone, bool], PipelineError]:
    for e in existing:
        if e.title == ms.title:
            print(f"  - exists: milestone #{e.gh_number} {e.title}")
            return Result.ok((ms.with_gh_number(e.gh_number or 0), False))
    if client.dry_run:
        print(f"  [dry-run] would create milestone: {ms.title}")
        return Result.ok((ms.with_gh_number(0), True))
    return client._run(
        "api", f"repos/{client.repo}/milestones",
        "-X", "POST",
        "-f", f"title={ms.title}",
        "-f", f"description={ms.description}",
    ).and_then(_parse_milestone_create_response).map(
        lambda n: (ms.with_gh_number(n), True)
    )



def _parse_milestone_create_response(stdout: str) -> Result[int, PipelineError]:
    try:
        data = json.loads(stdout)
        return Result.ok(int(data["number"]))
    except (json.JSONDecodeError, KeyError, ValueError) as e:
        return Result.err(PipelineError(
            error_type=ErrorType.PARSING_ERROR,
            message="could not extract milestone number from `gh api` response",
            cause=e,
        ))


def _find_or_create_issue(
    client: GitHubClient,
    issue: Issue,
    milestone_title: Optional[str],
    existing: list[Issue],
) -> Result[tuple[int, bool], PipelineError]:
    """Create `issue` if no existing issue has the same `[MN-k]` prefix.

    The prefix check is the idempotency guard: re-running populate after
    render has added new issues must not duplicate anything.  Comparing on
    the parsed ID rather than the full title makes the guard robust to
    post-creation title edits (which do happen — issue maintenance routinely
    tweaks the descriptive part of a title).

    The check runs ahead of the dry-run early-return so that `--dry-run`
    accurately previews idempotent behavior; existing issues are reported
    as `- exists`, only genuinely-new issues print `[dry-run] would create`.
    """
    for e in existing:
        if e.id == issue.id:
            print(f"  - exists: issue #{e.gh_number} {e.title}")
            return Result.ok((e.gh_number or 0, False))
    if client.dry_run:
        print(f"  [dry-run] would create issue: {issue.title}")
        return Result.ok((0, True))
    args = [
        "issue", "create",
        "--repo", client.repo,
        "--title", issue.title,
        "--body", issue.body,
    ]
    for label in issue.labels:
        args += ["--label", label]
    if milestone_title is not None:
        args += ["--milestone", milestone_title]
    return client._run(*args).and_then(_parse_issue_create_response).map(
        lambda n: (n, True)
    )



def _parse_issue_create_response(stdout: str) -> Result[int, PipelineError]:
    """`gh issue create` prints the issue URL; extract the trailing number."""
    m = re.search(r"/issues/(\d+)\s*$", stdout.strip())
    if not m:
        return Result.err(PipelineError(
            error_type=ErrorType.PARSING_ERROR,
            message="could not extract issue number from `gh issue create` output",
            context={"stdout": stdout},
        ))
    return Result.ok(int(m.group(1)))
