## scripts

This directory contains miscelleneous utility scripts.

The Python utilities live under `scripts/python/`, separated from shell scripts and other scaffolding so that they can be lifted as a self-contained package if and when they become useful outside this repository.  See `scripts/python/_utils/` for the functional-programming primitives (Result monad, command-runner wrappers, file-ops wrappers) shared across the Python scripts.

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

### Notes

- The script uses `env -u GH_TOKEN -u GITHUB_TOKEN` by default to work around
  token precedence issues.  Use `--no-env-prefix` to disable this.
- A 1.5-second delay between API calls avoids rate limiting (adjustable with `--delay`).
- Labels and milestones are idempotent — re-running skips existing ones.
- Issue titles are prefixed with `[M0-1]`, `[M1-2]`, etc. for easy identification.

