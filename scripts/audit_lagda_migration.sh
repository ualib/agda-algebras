#!/usr/bin/env zsh
# scripts/audit_lagda_migration.sh
#
# Answers the audit questions from issue #280 (M1-8):
#   1. How many .lagda files exist?
#   2. How many .agda files in src/ are skeletons (pragma + module + whitespace)?
#   3. How many .agda files have substantive content?
#   4. Which .lagda paths are referenced elsewhere in the repo?
#
# Run from the repo root.  Zero dependencies beyond zsh + standard coreutils.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

banner() { printf '\n━━━ %s ━━━\n' "$1"; }

banner "1. .lagda files under docs/lagda/"
LAGDA_COUNT=$(find docs/lagda -name '*.lagda' 2>/dev/null | wc -l | tr -d ' ')
print -- "  total .lagda files: $LAGDA_COUNT"
find docs/lagda -name '*.lagda' 2>/dev/null | sort > /tmp/lagda-files.txt
print -- "  list written to /tmp/lagda-files.txt"

banner "2. skeleton .agda files in src/"
# Heuristic for "skeleton": the file's non-comment, non-blank body consists
# of just a single module declaration and nothing else.  We strip line
# comments, block comments (approximately), and blank lines, then check
# whether what remains begins with 'module' and contains no '='.
SKELETON_COUNT=0
SUBSTANTIVE_COUNT=0
rm -f /tmp/skeleton.txt /tmp/substantive.txt
for f in $(find src -name '*.agda' -not -path '*/Legacy/*'); do
  body=$(sed -E -e 's|--.*$||' -e '/^\{-/,/-\}/d' "$f" \
          | awk 'NF' | sed -E 's/^\s+//;s/\s+$//')
  # A skeleton's body starts with OPTIONS pragma or "module ... where" and
  # contains no "=" signs (which would indicate a definition).
  if [[ -z "$body" ]] || ( ! grep -q '=' <<< "$body" ); then
    SKELETON_COUNT=$((SKELETON_COUNT + 1))
    print -- "$f" >> /tmp/skeleton.txt
  else
    SUBSTANTIVE_COUNT=$((SUBSTANTIVE_COUNT + 1))
    print -- "$f" >> /tmp/substantive.txt
  fi
done
print -- "  skeleton .agda files:    $SKELETON_COUNT  (list: /tmp/skeleton.txt)"
print -- "  substantive .agda files: $SUBSTANTIVE_COUNT  (list: /tmp/substantive.txt)"

banner "3. skeleton-to-.lagda pairing"
PAIRED=0
UNPAIRED=0
rm -f /tmp/unpaired-skeletons.txt
for f in $(cat /tmp/skeleton.txt 2>/dev/null); do
  # src/X/Y/Z.agda  →  docs/lagda/X/Y/Z.lagda
  rel=${f#src/}
  lagda="docs/lagda/${rel%.agda}.lagda"
  if [[ -f "$lagda" ]]; then
    PAIRED=$((PAIRED + 1))
  else
    UNPAIRED=$((UNPAIRED + 1))
    print -- "$f  (no $lagda)" >> /tmp/unpaired-skeletons.txt
  fi
done
print -- "  paired skeleton → .lagda: $PAIRED"
print -- "  unpaired skeletons:       $UNPAIRED  (list: /tmp/unpaired-skeletons.txt)"

banner "4. external references to .lagda paths"
print -- "  grepping for '\\.lagda' outside docs/lagda/ ..."
# Exclude the obvious places we expect matches (the files themselves,
# generated HTML archives, etc.) and focus on references that will need
# rewriting post-migration.
grep -rn '\.lagda\b' \
     --include='*.md' --include='*.yml' --include='*.yaml' \
     --include='Makefile' --include='*.mk' --include='*.sh' \
     --include='*.py' --include='*.bib' --include='README*' \
     --include='*.nix' \
     . 2>/dev/null \
  | grep -v '^docs/lagda/' \
  > /tmp/lagda-references.txt || true
REF_COUNT=$(wc -l < /tmp/lagda-references.txt | tr -d ' ')
print -- "  external .lagda references: $REF_COUNT  (list: /tmp/lagda-references.txt)"

banner "Agda 2.8.0 .lagda.md smoke test"
# Verify the minimal .lagda.md round-trips under the project's flags.
TMP=$(mktemp -d)
cat > "$TMP/Smoke.lagda.md" <<'EOF'
# Smoke test

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}
module Smoke where
data ⊤ : Set where tt : ⊤
```
EOF
if (cd "$TMP" && agda --html --html-dir="$TMP/out" Smoke.lagda.md \
                      >/dev/null 2>&1); then
  print -- "  .lagda.md smoke test: OK"
else
  print -- "  .lagda.md smoke test: FAILED — investigate before migrating"
fi
rm -rf "$TMP"

banner "Summary"
print -- "  .lagda files in docs/lagda/:            $LAGDA_COUNT"
print -- "  skeleton .agda files in src/:           $SKELETON_COUNT"
print -- "  substantive .agda files in src/:        $SUBSTANTIVE_COUNT"
print -- "  skeleton → .lagda pairs:                $PAIRED"
print -- "  skeletons lacking a paired .lagda:      $UNPAIRED"
print -- "  external .lagda references:             $REF_COUNT"
print -- ""
