---
name: typechecking-agda
description: Type-check Agda modules in the agda-algebras repository after editing any .lagda.md file, and verify the change meets the library's corpus-quality bar. Use whenever Agda source has been added or modified and needs validation before commit.
---

# Type-checking changes in agda-algebras

Type-checking is the only test this library has; a change is not done until it type-checks.

## Procedure

1. Enter the toolchain.  All Agda commands run inside the flake shell: `nix develop --command <cmd>`.  The flake pins Agda 2.8.0 and standard-library 2.3.
2. Check the edited module(s) first — fast, and it localizes errors: `nix develop --command agda src/Path/To/Module.lagda.md`.
3. Before committing, run the full check exactly as CI does: `nix develop --command make check`.
4. Do not stage generated artifacts (`*.agdai`, `Everything*.agda`, `/.agda/`); they are gitignored.

## Reading common Agda errors

+  Unsolved metas / yellow highlighting: a term's type is under-determined; add an explicit type signature or annotate the ambiguous argument.
+  "x != y of type T": a definitional-equality mismatch; check whether the development expects setoid equality (`Setoid/`) rather than propositional `_≡_`.
+  "No instance of ...": a missing import, or an instance argument not in scope.
+  Scope error after a rename: confirm the symbol is not part of an in-flight deprecation (`∣_∣` / `∥_∥` → `proj₁` / `proj₂`).

## Quality gate (verify before declaring done)

+  Every new public definition has an explicit type signature.
+  New lemmas are named, not inlined into opaque `rewrite` chains.
+  No new synonym was introduced for an existing concept.
+  Inline Agda names in prose use kramdown spans, e.g. `` `S`{.AgdaFunction} ``.


