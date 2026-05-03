#!/usr/bin/env bash
# scripts/freeze_base_to_legacy.sh
#
# Why this exists:
#   M2-1 ratifies Setoid/ as canonical and freezes Base/ as Legacy/Base/.
#   This script performs the mechanical part: git mv the tree, then rewrite
#   every reference to "Base." in import lines and module headers to
#   "Legacy.Base.". Run with --dry-run first to inspect the diff.
#
# Why a script and not a sed one-liner:
#   We rewrite three distinct syntactic positions (module header, open import,
#   import) and we want to leave prose, comments, and link targets alone unless
#   they are unambiguously module references. A script makes each transformation
#   reviewable and reversible.

set -euo pipefail

DRY_RUN=${1:-}

run() {
  if [[ "$DRY_RUN" == "--dry-run" ]]; then
    echo "DRY: $*"
  else
    eval "$@"
  fi
}

# 1. Move the tree.
if [[ -d src/Base ]]; then
  run "mkdir -p src/Legacy"
  run "git mv src/Base src/Legacy/Base"
fi

# 2. Move the top-level src/Base.lagda.md to src/Legacy/Base.lagda.md
if [[ -f src/Base.lagda.md ]]; then
  run "git mv src/Base.lagda.md src/Legacy/Base.lagda.md"
fi

# 3. Rewrite references. We target three patterns:
#    (a) `module Base.X.Y where`             → `module Legacy.Base.X.Y where`
#    (b) `open import Base.X.Y`              → `open import Legacy.Base.X.Y`
#    (c) `import Base.X.Y`                   → `import Legacy.Base.X.Y`
#
# Limit the search to .agda, .lagda, .lagda.md files inside src/.

FILES=$(find src -type f \( -name '*.agda' -o -name '*.lagda' -o -name '*.lagda.md' \))

for f in $FILES; do
  # (a) module header
  run "sed -i.bak -E 's/^(\s*module\s+)Base\./\1Legacy.Base./' '$f'"
  # (b) and (c) imports
  run "sed -i.bak -E 's/^(\s*open\s+import\s+)Base\./\1Legacy.Base./' '$f'"
  run "sed -i.bak -E 's/^(\s*import\s+)Base\./\1Legacy.Base./' '$f'"
  run "rm -f '${f}.bak'"
done

# 4. Top-level aggregator.
#    src/agda-algebras.agda (or .lagda.md) imports `Base` and `Setoid` (and others).
#    Rewrite the `Base` line to `Legacy.Base`. Done by hand if the aggregator is unusual.
echo "Don't forget to update src/agda-algebras.agda by hand: see suggested diff in the PR description."
