## scripts

This directory contains miscellaneous utility scripts.

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

---

### `unused_imports`: flagging unused imports and open statements

This script statically analyses the literate Agda corpus and reports names that
a module brings into scope with an `import` / `open` statement but never uses.
Pruning these keeps the dependency surface of each module honest and the corpus
tidy.

**Prerequisites**.

+  Python 3.10+ (uses structural `match`); no third-party packages.

**Example Usage**.

+  Scan the canonical tree (skips the frozen `src/Legacy`), printing one line per
   finding plus a summary:

   ```zsh
   python3 scripts/python/unused_imports.py            # defaults to src/
   make unused-imports                                  # equivalent
   ```

+  Scan a single subtree or file:

   ```zsh
   python3 scripts/python/unused_imports.py src/Setoid
   python3 scripts/python/unused_imports.py src/Overture/Basic.lagda.md
   ```

+  Machine-readable output, summary only, or also listing the whole-module opens
   that cannot be analysed:

   ```zsh
   python3 scripts/python/unused_imports.py --json src
   python3 scripts/python/unused_imports.py --summary src
   python3 scripts/python/unused_imports.py --show-open-ended src
   ```

The exit status is `1` when anything is flagged and `0` otherwise, so the tool
can gate CI; pass `--exit-zero` to suppress that, and `--include-legacy` to scan
`src/Legacy` as well.

**What it does and does not flag**.

+  It reports the *closed* forms whose in-scope names it can enumerate exactly:
   `using (…)` lists (per name), `using () renaming (…)`, `as N` aliases, and
   bare qualified `import M` / `import M as N`.
+  It never flags `public` re-exports, nor the open-ended forms (a whole-module
   `open import M` with no `using`, `hiding (…)`, or a bare `renaming (…)`);
   those bring in a set of names a textual tool cannot enumerate and are listed
   only under `--show-open-ended`.
+  A mixfix name such as `_∙_` counts as used when its operator part appears at a
   use site (`x ∙ y`); a `Foo-syntax` name counts as used when its `syntax`
   notation `Foo[ … ]` appears; a `module X` brought into scope counts as used
   when it is later re-opened with `open X …`.

**Caveats**.

The analysis is textual, and tuned to avoid false positives — every genuine use
produces a token it counts, so it errs toward leaving a borderline import alone.
Two residual cases can still be reported in error and should be verified with a
type-check before removal: a name resolved only by *instance search*, and a name
referenced only inside a `{-# … #-}` pragma (pragmas are stripped with comments).
The analyzer ships with a test suite:

```zsh
python3 scripts/python/test_unused_imports.py          # or: make unused-imports-test
```

