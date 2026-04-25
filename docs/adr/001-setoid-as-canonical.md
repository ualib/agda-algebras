# ADR-001: Setoid as canonical development tree for 3.0

## Status

Accepted — 2026-04-24.

## Context

Through the 2.x line, `agda-algebras` carried two parallel developments of universal algebra: `src/Base/`, a standard dependent-types formulation that predates setoid machinery, and `src/Setoid/`, a setoid-based reconstruction built for the TYPES 2021 proof of Birkhoff's HSP theorem.  The two trees share the same vocabulary — `Algebra`, `Hom`, `Con`, `Subalgebra` — but with incompatible underlying types: `Base/` uses propositional equality on raw domain types, `Setoid/` uses setoid equivalence.

Maintaining two parallel foundations through the 3.0 cycle would double the cost of every theorem added under `Classical/` or `Cubical/` and would leave new contributors without a clear answer to the question "which tree does my work land in?"  A single canonical foundation is required.

The trade-off between `Base/` and `Setoid/` is substantive rather than cosmetic.  `Base/` is simpler to read and closer to how universal algebra is typically presented in type theory; it suffices for the portion of the library that terminates at Birkhoff, which is what most published work in this repository actually uses.  `Setoid/`, on the other hand, is fully constructive — it does not postulate extensionality — and it matches the idiom of stdlib's `Algebra.Bundles`, which is where any future stdlib-interoperable classical-structure development must land.  `Setoid/` also already contains the only fully constructive proof of the HSP theorem in Martin–Löf type theory.

A third consideration, previously under-emphasized: definitions in `Setoid/` that are expressed purely in terms of the `Algebra.Domain` equivalence — rather than propositional equality — port mechanically to a Cubical formulation in which the equivalence is replaced by a path type.  This is the substrate on which ADR-003 (Cubical as long-term target) rests.

## Decision

`src/Setoid/` is the canonical development tree for the 3.0 release.  New work lands there.  `src/Base/` is frozen: it is moved to `src/Legacy/Base/`, kept type-checking, and receives no new development.  Legacy contents may be ported forward to `Setoid/` (or, eventually, `Cubical/`) as specific theorems are needed in the canonical tree.

## Consequences

+  **The "which tree does my work go in" question has a one-word answer for the entire 3.0 cycle.**  Contributor onboarding simplifies.  The style guide, README, and CONTRIBUTING file speak from a single foundation.
+  **The Classical layer (M3) builds cleanly on top.**  `Classical/` is designed around the `Setoid.Algebras.Basic.Algebra` record; the Σ-typed classical structures and record-typed bundle views (ADR-002) would be materially more awkward over `Base/`, whose equational machinery fights stdlib's setoid-shaped bundles.
+  **The Cubical track (M5) is reachable without an additional rewrite.**  The setoid equivalence and the path equality of cubical Agda are exchangeable at the level of definitions that never mention the underlying equality directly.  The eventual 4.0 Cubical port is thus substantively mechanical rather than a second full redevelopment.
+  **Downstream users of `Base/` must migrate.**  This is a breaking change for anyone depending on the library's pre-3.0 API surface.  The move is announced in CHANGELOG, `Base/` remains available under `Legacy/Base/`, and deprecation notes inside `Legacy/Base/` point to the canonical alternatives where they exist.
+  **`Base/` must be kept type-checking for posterity.**  Frozen-but-checked means the CI pipeline must run over both trees indefinitely, at the cost of some build time.  The alternative — deleting `Base/` — was rejected because the Base-tree proofs remain the only implementations of several lemmas that have not yet been ported, and because the historical TYPES 2021 proof should remain executable at its original location as a matter of scholarly record.
+  **Some readable but pedagogically useful Base-tree presentations are demoted to Legacy.**  `Base.Varieties.FreeAlgebras.Birkhoff` is the clearest example.  The compensation is `Demos/HSP`, which is kept as a self-contained teaching artifact (M2-4).

## Alternatives considered

+  **Keep both `Base/` and `Setoid/` as co-canonical**.  Rejected because this is what the 2.x line did, and the cost of every new theorem being built twice is precisely what motivated the reconstruction.  There is no mathematical case for carrying both indefinitely once the Classical and Cubical tracks exist.
+  **Delete `Base/` outright**.  Rejected because (i) several theorems live only in `Base/` and would be lost until re-proven, and (ii) the TYPES 2021 citations in the literature point at `Base/`-tree modules whose URLs should continue to resolve.  Freezing under `Legacy/Base/` preserves both.
+  **Adopt `Base/` as canonical, reconstruct `Setoid/` as a translation layer**.  Rejected because `Setoid/` already contains the definitive HSP proof, matches stdlib's bundle idiom, and keeps the door open to cubical Agda — three forward-looking properties that `Base/` does not have.

## References

+  Issue M2-1 — [Freeze Base/, adopt Setoid/ as canonical](https://github.com/ualib/agda-algebras/issues/256).
+  `docs/STYLE_GUIDE.md` — section on record vs Σ, which depends on this decision.
+  `docs/GITHUB_PROJECT.md` — milestone 2 exit criterion.
+  DeMeo and Carette (2023), *A Machine-Checked Proof of Birkhoff's Variety Theorem in Martin-Löf Type Theory*, TYPES 2021 post-proceedings.


