#!/usr/bin/env bash
#
# File: scripts/audit_lagda_migration.sh
#
# Answers the audit questions from issue #280 (M1-8):
#   1. How many .lagda files exist?
#   2. How many .agda files in src/ are skeletons (pragma + module + whitespace)?
#   3. How many .agda files have substantive content?
#   4. Which .lagda paths are referenced elsewhere in the repo?
#
# Run from the repo root.  External dependencies: bash 4+, git, agda
# (for the smoke test only), and the standard POSIX text utilities sed,
# awk, grep, find, wc, tr, stat, mktemp.  Tested under Ubuntu 24.04;
# a portability shim is used for stat(1) so the script also works on
# macOS / BSD.


set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

# All output files live under a per-run temporary directory.  The path
# is printed at the end of the run so the user knows where to find
# /skeleton.txt, /substantive.txt, etc.
OUT_DIR="$(mktemp -d -t agda-algebras-audit-XXXXXX)"

# Portable file-mtime in seconds since the epoch.  GNU stat uses
# `-c %Y`, BSD/macOS stat uses `-f %m`.  Rather than detect which
# variant is in scope, shell out to Python — it's available on every
# platform agda-algebras supports and produces consistent output.
file_mtime() { python3 -c 'import os, sys; print(int(os.path.getmtime(sys.argv[1])))' "$1"; }

banner() { printf '\n━━━ %s ━━━\n' "$1"; }

banner "1. .lagda files under docs/lagda/"
LAGDA_COUNT=$(find docs/lagda -name '*.lagda' 2>/dev/null | wc -l | tr -d ' ')
printf '%s\n' "  total .lagda files: $LAGDA_COUNT"
find docs/lagda -name '*.lagda' 2>/dev/null | sort > "$OUT_DIR/lagda-files.txt"
printf '%s\n' "  list written to $OUT_DIR/lagda-files.txt"

banner "2. skeleton .agda files in src/"
# Heuristic for "skeleton": after stripping
#   - whole-line OPTIONS pragmas    {-# OPTIONS ... #-}
#   - line comments                  -- ...
#   - block comments                 {- ... -}
#   - blank lines
# the file's body should be exactly one line: the `module X where`
# declaration.  Any further surviving line (an import, a definition,
# anything) marks the file as substantive.
#
# Stripping OPTIONS pragmas explicitly is necessary because they begin
# with `{-`, which would otherwise be interpreted as the start of a
# block-comment range by sed.
SKELETON_COUNT=0
SUBSTANTIVE_COUNT=0
rm -f "$OUT_DIR/skeleton.txt" "$OUT_DIR/substantive.txt" "$OUT_DIR/substantive-paired.txt"
for f in $(find src -name '*.agda' -not -path '*/Legacy/*'); do
  body=$(sed -E \
              -e 's|^[[:space:]]*\{-#[[:space:]]*OPTIONS[^}]*#-\}[[:space:]]*$||' \
              -e 's|--.*$||' \
              -e '/^[[:space:]]*\{-([^#]|$)/,/-\}/d' "$f" \
          | awk 'NF' | sed -E 's/^[[:space:]]+//;s/[[:space:]]+$//')
  first_line=$(printf '%s\n' "$body" | sed -n '1p')
  line_count=$(printf '%s\n' "$body" | awk 'NF { count++ } END { print count + 0 }')
  # After comment-stripping, a "skeleton" should have exactly one
  # surviving line: the `module X where` declaration.  The OPTIONS
  # pragma was already deleted; any imports or definitions push the
  # line count above 1 and mark the file as substantive.
  if [[ "$line_count" -eq 1 ]] \
     && grep -Eq '^module[[:space:]]+.+[[:space:]]+where$' <<< "$first_line"; then
    SKELETON_COUNT=$((SKELETON_COUNT + 1))
    printf '%s\n' "$f" >> "$OUT_DIR/skeleton.txt"
  else
    SUBSTANTIVE_COUNT=$((SUBSTANTIVE_COUNT + 1))
    printf '%s\n' "$f" >> "$OUT_DIR/substantive.txt"
  fi
done
printf '%s\n' "  skeleton .agda files:    $SKELETON_COUNT  (list: $OUT_DIR/skeleton.txt)"
printf '%s\n' "  substantive .agda files: $SUBSTANTIVE_COUNT  (list: $OUT_DIR/substantive.txt)"

banner "3. .agda-to-.lagda pairing (all files, not just skeletons)"
PAIRED=0
UNPAIRED=0
SUBSTANTIVE_PAIRED=0
rm -f "$OUT_DIR/unpaired-skeletons.txt" "$OUT_DIR/substantive-paired.txt"
for f in $(cat "$OUT_DIR/skeleton.txt" 2>/dev/null); do
  # src/X/Y/Z.agda  →  docs/lagda/X/Y/Z.lagda
  rel=${f#src/}
  lagda="docs/lagda/${rel%.agda}.lagda"
  if [[ -f "$lagda" ]]; then
    PAIRED=$((PAIRED + 1))
  else
    UNPAIRED=$((UNPAIRED + 1))
    printf '%s\n' "$f  (no $lagda)" >> "$OUT_DIR/unpaired-skeletons.txt"
  fi
done
printf '%s\n' "  paired skeleton → .lagda: $PAIRED"
printf '%s\n' "  unpaired skeletons:       $UNPAIRED  (list: $OUT_DIR/unpaired-skeletons.txt)"

# DRIFT HAZARD: substantive .agda files that ALSO have a .lagda partner.
# These are the files where prose and code may have desynchronized.
for f in $(cat "$OUT_DIR/substantive.txt" 2>/dev/null); do
  rel=${f#src/}
  lagda="docs/lagda/${rel%.agda}.lagda"
  if [[ -f "$lagda" ]]; then
    SUBSTANTIVE_PAIRED=$((SUBSTANTIVE_PAIRED + 1))
    agda_size=$(wc -l < "$f")
    lagda_size=$(wc -l < "$lagda")
    agda_mtime=$(file_mtime "$f")
    lagda_mtime=$(file_mtime "$lagda")
    delta=$((agda_mtime - lagda_mtime))
    printf '%s\n' "$f  ($agda_size lines)  vs  $lagda  ($lagda_size lines)  Δmtime=${delta}s" \
      >> "$OUT_DIR/substantive-paired.txt"
  fi
done
printf '%s\n' "  substantive .agda WITH a .lagda partner (drift hazard): $SUBSTANTIVE_PAIRED"
if [[ $SUBSTANTIVE_PAIRED -gt 0 ]]; then
  printf '%s\n' "  (list: $OUT_DIR/substantive-paired.txt)"
fi

banner "4. external references to .lagda paths"
printf '%s\n' "  grepping for '\\.lagda' outside docs/lagda/ ..."
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
  > "$OUT_DIR/lagda-references.txt" || true
REF_COUNT=$(wc -l < "$OUT_DIR/lagda-references.txt" | tr -d ' ')
printf '%s\n' "  external .lagda references: $REF_COUNT  (list: $OUT_DIR/lagda-references.txt)"

banner "Agda 2.8.0 .lagda.md smoke test"
# Verify the minimal .lagda.md round-trips under the project's flags.
# Use --no-libraries so the project's include path doesn't try to
# resolve the temp module against stdlib or src/.
TMP=$(mktemp -d)
cat > "$TMP/Smoke.lagda.md" <<'EOF'
# Smoke test

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}
module Smoke where
data ⊤ : Set where tt : ⊤
```
EOF
if (cd "$TMP" && agda --no-libraries --html --html-dir="$TMP/out" \
                      Smoke.lagda.md >/dev/null 2>&1); then
  printf '%s\n' "  .lagda.md smoke test: OK"
else
  printf '%s\n' "  .lagda.md smoke test: FAILED — investigate before migrating"
fi
rm -rf "$TMP"

banner "Summary"
printf '%s\n' "  .lagda files in docs/lagda/:            $LAGDA_COUNT"
printf '%s\n' "  skeleton .agda files in src/:           $SKELETON_COUNT"
printf '%s\n' "  substantive .agda files in src/:        $SUBSTANTIVE_COUNT"
printf '%s\n' "  skeleton → .lagda pairs:                $PAIRED"
printf '%s\n' "  skeletons lacking a paired .lagda:      $UNPAIRED"
printf '%s\n' "  substantive .agda WITH .lagda partner:  $SUBSTANTIVE_PAIRED  (drift hazard)"
printf '%s\n' "  external .lagda references:             $REF_COUNT"
printf '\n%s\n' "Output files: $OUT_DIR"
