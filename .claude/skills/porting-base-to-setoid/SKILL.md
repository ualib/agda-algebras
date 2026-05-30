---
name: porting-base-to-setoid
description: Port a frozen Legacy.Base module into the canonical Setoid/ tree — classify the module, build or extend its Setoid analog over setoid equality, and rewire imports off Legacy.Base. Use whenever a module in Setoid/, Examples/, or Exercises/ still imports Legacy.Base.* (including the remaining M2-8 import fixes), or when M9 calls for porting the Continuous/Complexity relations.
---

# Porting Legacy.Base modules to Setoid/

`Setoid/` is the canonical tree; `Legacy/Base/` is frozen.  The invariant: no module should import `Legacy.Base.*`.  M2-6 / M2-7 established this for `Setoid/`; the remaining M2-8 fixes extend it to `Examples/` and `Exercises/`.  Port deliberately — not every frozen module should be reproduced one-to-one.

## Step 0 — Classify before porting

From the M2-1 inventory (~33 of 68 Base modules already have a Setoid analog; 35 are orphans), decide where the module belongs:

+  `Equality.*`: retired by construction.  Do not port — setoid equality replaces it.
+  `Structures.*`: belongs in the planned `Classical/` tree as a specific theory (Σ-type core with a record bundle view), not a flat `Setoid/` port.  Follow the new-module scaffolding conventions.
+  `Complexity/`, `Continuous/`: M9 scope.  Port only when the milestone calls for it (e.g. `Relations.Continuous` feeds M9-1).
+  `Adjunction/`, `Categories/`: placement is TBD.  Confirm the target before porting.
+  Otherwise: port into `Setoid/` as the canonical analog.

## Step 1 — Reuse, don't recreate

If a `Setoid/` analog already exists, the task is usually to extend it and remove its remaining `Legacy.Base.*` dependency — not to rewrite it.  Check first.

## Step 2 — Replace propositional equality with setoid equality

+  Carriers become `Setoid`s; propositional `_≡_` reasoning becomes the carrier's `_≈_` with its `IsEquivalence`.
+  Functions must respect `_≈_`: what was `cong` / `subst` over `_≡_` becomes the explicit congruence obligation of a setoid `Func`.
+  Operations carry their respect-for-`_≈_` proofs; thread these rather than leaning on definitional equality.

## Step 3 — Apply in-flight deprecations as you go

+  Replace `∣_∣` / `∥_∥` with `proj₁` / `proj₂`.

## Step 4 — Rewire imports

+  Point every import at the `Setoid/` counterpart and eliminate `Legacy.Base.*` imports.  Removing the last such import from a module is the concrete M2-6 win.

## Step 5 — Type-check and gate quality

+  Type-check per-file, then `make check`.
+  Verify: explicit type signatures, small named lemmas (no opaque `rewrite` chains), one canonical name per concept (no synonyms), a prose comment paired with each statement, and kramdown name spans in the prose.

This is the general recipe; tune the per-group specifics to the actual module.


