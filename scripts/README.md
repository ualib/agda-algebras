## scripts

This directory contains miscelleneous utility scripts.

The Python utilities live under `scripts/python/`, separated from shell scripts and other scaffolding so that they can be lifted as a self-contained package if and when they become useful outside this repository.  See `scripts/python/_utils/` for the functional-programming primitives (Result monad, command-runner wrappers, file-ops wrappers) shared across the Python scripts.

---

### `gh_project_populate`: automating GitHub project creation

This script is used to create a GitHub project, issues, and labels for a repository
from a single markdown file using the GitHub API.

**Prerequisites**.

- Python 3.8+
- `gh` CLI installed and authenticated

**Example Usage**.

The following commands assume the GitHub project/issue generation script is at
`scripts/python/gh_project_populate.py` and the Markdown file containing the
label/project/issue descriptions is `docs/GITHUB_PROJECT.md`.

+  Dry run — see what would be created (from the main project directory).

   ```zsh
   python3 scripts/python/gh_project_populate.py docs/GITHUB_PROJECT.md --repo ualib/agda-algebras --dry-run
   ```

+  Create everything (will prompt for confirmation).


   ```zsh
   python3 scripts/python/gh_project_populate.py docs/GITHUB_PROJECT.md --repo ualib/agda-algebras
   ```

+  Or create in stages.

   ```zsh
   python3 scripts/python/gh_project_populate.py docs/GITHUB_PROJECT.md --repo ualib/agda-algebras --labels-only
   python3 scripts/python/gh_project_populate.py docs/GITHUB_PROJECT.md --repo ualib/agda-algebras --milestones-only
   python3 scripts/python/gh_project_populate.py docs/GITHUB_PROJECT.md --repo ualib/agda-algebras --issues-only
   ```

+  Resume if interrupted (e.g., start from issue M1-3).

   ```zsh
   python3 scripts/python/gh_project_populate.py docs/GITHUB_PROJECT.md --repo ualib/agda-algebras --issues-only --start-from M1-3
   ```

---

### `gh_project_render`: regenerating GITHUB_PROJECT.md from GitHub

Once the project is bootstrapped, GitHub becomes the source of truth for issue state.  This script pulls live GitHub state and regenerates the issue listings inside `docs/GITHUB_PROJECT.md`, leaving hand-edited prose (milestone descriptions, exit criteria, mermaid graphs) untouched.

The file is treated as a sequence of manual prose segments interleaved with regions delimited by HTML-comment markers:

```markdown
<!-- BEGIN GENERATED: milestone-1 -->
...
<!-- END GENERATED: milestone-1 -->
```

Render preserves manual segments byte-for-byte and rebuilds each generated region from the live GitHub API.  The convention is that a region with id `milestone-N` is rebuilt from issues bearing the `milestone-N-*` label, ordered by their `[MN-k]` ordinal.

**Example Usage**.

+  Regenerate in place:

   ```zsh
   make project-plan
   ```

+  Or run the script directly:

   ```zsh
   python3 scripts/python/gh_project_render.py docs/GITHUB_PROJECT.md --repo ualib/agda-algebras
   ```

+  Verify staleness without rewriting (intended for CI):

   ```zsh
   python3 scripts/python/gh_project_render.py docs/GITHUB_PROJECT.md --repo ualib/agda-algebras --check
   ```

**The populate / render symmetry**.

The two scripts cover disjoint phases of the project's life cycle: populate is the one-shot bootstrap from a hand-authored markdown plan to GitHub project state; render is the steady-state inverse, pulling live GitHub state back into the same markdown.  After bootstrap, manual edits to issue bodies should happen on GitHub; the next `make project-plan` propagates them back into `GITHUB_PROJECT.md`.

---

### Notes

- The script uses `env -u GH_TOKEN -u GITHUB_TOKEN` by default to work around
  token precedence issues.  Use `--no-env-prefix` to disable this.
- A 1.5-second delay between API calls avoids rate limiting (adjustable with `--delay`).
- Labels and milestones are idempotent — re-running skips existing ones.
- Issue titles are prefixed with `[M0-1]`, `[M1-2]`, etc. for easy identification.

