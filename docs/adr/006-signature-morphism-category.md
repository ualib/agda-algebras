<!-- File: docs/adr/006-signature-morphism-category.md -->

# ADR-006: Signature morphisms and the self-contained `Sig` category

## Status

Accepted — 2026-06-07 (M4-5a).
Amended — 2026-06-14 (M4-16, #403): the `reduct` development relocates from `Classical/` to `Setoid/` (reduct is universal algebra, not classical, and depends on nothing in `Classical/`).  See the *Amendment* section below; it supersedes the placement clause of Decision 3.

## Context

[M4-5][] (#338) builds out the category-theoretic layer the foundation already implicitly is: `Signature` is a container, `⟨ 𝑆 ⟩` is its polynomial functor, `Interp` is the structure map, and `Term` is the initial algebra.  [M4-5a][] (#339) is the first link: package the pair `(ι , κ)` that `reduct` consumes today (then `Classical.Structures.Reduct`, relocated to `Setoid.Algebras.Reduct` by the *Amendment* below) as a first-class `SigMorphism 𝑆₁ 𝑆₂` — a container morphism with `ι` covariant on operation symbols and `κ` contravariant on positions — and assemble signatures and these morphisms into a category `Sig`.

Two decisions are forced before any of [M4-5][] can proceed, because they fix the shape of everything downstream.

+  **Morphism equality**.  Under `--safe` without funext, two morphisms agreeing pointwise need not be propositionally equal — the same `Fin n` η-gap that forces *pointwise* round-trips at the stdlib bundle bridges (ADR-002 §6).  Issue #339 flagged that the category laws might therefore have to be stated against a *hom-setoid* rather than `_≡_`.  Settling this is half the value of the issue.
+  **Realization**.  Build the category on the `agda-categories` library (as a `Category` instance) or stay self-contained?  `agda-categories` is *not* a dependency of the flake, which pins only Agda 2.8.0 and standard-library 2.3.

## Decision

1.  **The signature category uses propositional `_≡_` for morphism equality; no hom-setoid**.  The module `Overture.Signatures.Morphisms` confirms that all three category laws (left identity, right identity, associativity) hold by `refl`.  The reason: `ι` and `κ` are plain functions, so the identity morphism is `id` on both components and composition is ordinary function composition; function η reduces `f ∘ id`, `id ∘ f`, and `(f ∘ g) ∘ h` definitionally, and record η lifts the componentwise equalities to the `SigMorphism` record.  The `Fin n` η-gap does **not** arise, because the laws compose *abstract* position maps and never normalize a `Fin`-pattern lambda.  This conclusion is specific to the signature category, where morphisms are bare functions; it does **not** transfer to the category of algebras ([M4-5c][]), where homomorphism equality is pointwise and a hom-setoid is required.

2.  **Realize the [M4-5][] category layer self-contained; do not add an `agda-categories` dependency**.  Because the laws are `refl`/`cong`, the realization cost `agda-categories` would save is small, and the dependency cost is real (a flake change, a version pin, CI surface, and unverified compatibility with the pinned Agda 2.8.0).  The shared category vocabulary the layer introduces — built where [M4-5c][] first needs it, not here — is a *minimal* `Category` record carrying a hom-equality field `_≈_`, instantiated to `_≈_ = _≡_` for `Sig` and to a pointwise setoid for the algebra category.

3.  **The signature-morphism layer is setoid-free and lives in `Overture`**.  Objects are Σ-typed signatures, morphisms are functions, and equality is `_≡_` — no `Setoid` machinery is involved — so the module is `Overture.Signatures.Morphisms`, co-located with `Overture.Signatures`.  The algebra-level category material ([M4-5c][] onward) lives higher up, in the `Setoid/` layer.  `reduct`, which acts on algebras, stays in its current home and merely imports the morphism type (acyclically: `Overture` is below `Setoid` and `Classical`).  *(The placement of `reduct` is amended by [M4-16][] — see the Amendment below: `reduct` and its dependent modules move down into `Setoid/`, which is both the principled home and cycle-free, since they import nothing from `Classical/`.)*

4.  **`Sig 𝓞 𝓥` fixes a common level pair**.  Its objects are `Signature 𝓞 𝓥` at fixed `(𝓞 , 𝓥)`; the morphism record shares those levels.  A level-heterogeneous (large or displayed) category of signatures is out of scope for [M4-5a][].

5.  **`reduct` is re-expressed to consume a `SigMorphism`, keeping the `(ι , κ)`-pair form as a thin wrapper (`reductBy`)**.  Each of the six call sites routes its existing per-structure position map — `∙-κ`, `mo-κ`, `∧-κ`, `∨-κ`, `+-κ`, `·-κ`, each defined by pattern-matching on the operation symbol and returning `id` — through `reductBy`, a one-line change per site.  A single generic `embed` with `κ = λ _ → id` is *not* definable under `--safe`: for an abstract symbol `o`, the arities `ArityOf 𝑆₂ (ι o)` and `ArityOf 𝑆₁ o` are not definitionally equal, so `id` does not type-check there; the position map must pattern-match on the symbol, which is exactly what the per-structure maps already do.

## Consequences

+  **`Sig` is the cheapest possible category to certify**.  The laws are `refl`, so the functor and naturality results of [M4-5b][] sit on a strict base, and anything that stays at the signature level gets congruence and rewriting directly, with no setoid-reasoning overhead.
+  **No new toolchain dependency**.  The flake's minimal, carefully-pinned surface is preserved, and the cubical port (ADR-003) stays under our control rather than gated on `agda-categories`' cubical compatibility.
+  **We forgo `agda-categories`' library of constructions** (negative).  Functor categories, (co)limits, and adjunction combinators are not handed to us; [M4-5d][] (the `F ⊣ reduct` adjunction) and later issues may have to build scaffolding `agda-categories` would have supplied.  Revisit decision 2 if the self-contained vocabulary grows unwieldy.
+  **The signature and algebra categories use different hom-equalities** (negative).  `Sig` uses `_≡_`; the algebra category will use a pointwise setoid.  The shared `Category` record must therefore be general (carry `_≈_`) even though `Sig` only ever needs `_≡_`, so a reader meeting `Sig` first sees a `_≈_` field that is trivially `_≡_`.
+  **Placement in `Overture` keeps the signature category dependency-light**.  It is importable by the whole library without pulling in `Setoid` machinery.
+  **`reduct`'s call sites migrate uniformly**.  `lattice→meetMagma`, `lattice→joinMagma`, `monoid→magma`, `group→monoidAlg`, `ring→abelianGroupAlg`, and `ring→monoidAlg` each route their existing pattern-matched position map through the `reductBy` wrapper — a one-line change per site, no flag-day rewrite.

## Alternatives considered

+  **A hom-setoid for `Sig` from the start**.  Rejected: the spike shows `_≡_` suffices with `refl` laws, so a hom-setoid would be unjustified overhead at the signature level.  It remains the right choice for the *algebra* category, for the different reason that homomorphism equality is pointwise; that is recorded when [M4-5c][] lands.
+  **Build on `agda-categories`**.  Rejected as the default: it is not a flake dependency, so adopting it is a toolchain change with a version pin, CI surface, and unverified Agda-2.8.0 compatibility (it has historically lagged Agda releases), in exchange for realization savings that are small when the laws are `refl`/`cong`.  The option stays open as a later, separately-decided spike if the self-contained vocabulary proves insufficient.
+  **Place the signature category under `Setoid/`**.  Rejected: the signature category needs no setoids, so `Overture` is its natural, lower home and keeps it usable without `Setoid` imports.
+  **A level-heterogeneous (large) category of signatures**.  Deferred: useful for morphisms across differing operation/arity levels, but not needed for reduct-packaging goal of [M4-5a][]; the fixed-level `Sig 𝓞 𝓥` is the clean first cut.

## Amendment (2026-06-14, M4-16): the reduct development moves to `Setoid/`

Decision 3 placed `reduct` in `Classical.Structures.Reduct`, and the reduct functor and reduct-invariance results were realized in `Classical/` too, on the rule that "anything whose object map is `reduct` must live in `Classical/` — a `Setoid.* → Classical.*` import would be a cycle."  [M4-16][] (#403) reverses the placement, for two reasons.

+  **Conceptual.**  Reducts, signature morphisms, and varieties are *universal algebra* — they range over arbitrary signatures.  `Classical/` is the tradition of specific structures (groups, rings, fields), each studied over one fixed signature, where reducts play little role.  So the reduct development belongs in the `Setoid/` foundation.

+  **Technical — the cycle rule was circular.**  `reduct` imports only `Overture.*` and `Setoid.Algebras.Basic`; it depends on nothing in `Classical/`.  The "`Setoid → Classical` cycle" existed *only because* `reduct` was parked in `Classical/`.  Moving the root down removes the obstruction entirely, and reunifies the M4-5 functorial layer — most of which (`Overture.Signatures.Morphisms`, `Setoid.Signatures.Functor`, the `Setoid.Categories.*` vocabulary, `Overture.Terms.Translation`, `Setoid.Terms.*`) already lives in `Setoid/` / `Overture/`; only the reduct-touching modules were stranded in `Classical/`.

The relocations:

+  `Classical.Structures.Reduct` → `Setoid.Algebras.Reduct`.
+  `Classical.Categories.Reduct` → `Setoid.Categories.Reduct`.
+  `Classical.Varieties.Invariance` → `Setoid.Varieties.Invariance`, and `Classical.Varieties.Reducts` → `Setoid.Varieties.Reducts` (the M4-5g module, #402), retiring the `Classical/Varieties/` subtree.

What stays in `Classical/`: `Classical.Categories.AdjoinUnit` and `Classical.Categories.Forgetful`, which are structure-specific (adjoin-a-unit to a semigroup; `monoid→semigroup`) and now import `reductF` / `⊧-reduct` from their `Setoid/` homes.  The classical forgetful projections (`monoid→semigroup`, `group→monoid`, …) continue to consume `reduct` / `reductBy`, now imported from `Setoid.Algebras.Reduct`.

Because the moved modules are inherently *two-signature* (`φ : 𝑆₁ → 𝑆₂`), they do not fit the single-`{𝑆}` umbrella aggregators `Setoid.Algebras` and `Setoid.Varieties`; they remain directory-resident and are imported directly, as they already were.  Decision 2 (self-contained, no `agda-categories`) and the equality decisions (1, 4) are unaffected; only the *tree* placement of the reduct modules changes.

## References

+  Issue [M4-5][] — Signatures as functors: reducts, expansions, and interpretability.
+  Issue [M4-16][] — Relocate the reduct development from `Classical/` to `Setoid/` (this amendment).
+  Issue [M4-5a][] — Category of signature morphisms.
+  `src/Overture/Signatures/Morphisms.lagda.md` — the `SigMorphism` record, identity and composition, and the `refl`-proved category laws (the spike this ADR records).
+  `docs/notes/milestone-signature-functors.md` — the [M4-5][] design note.
+  ADR-002 §6 — pointwise equivalence and the `Fin n` η-gap at the bundle bridges (the obstruction that does not recur at the signature level).
+  ADR-003 — Cubical Agda as the long-term target (the portability the self-contained choice keeps under our control).
+  ADR-005 — the `𝓞` / `𝓥` convention the new module follows (imports the levels, never re-declares them).
+  M. Abbott, T. Altenkirch, N. Ghani, *Containers: constructing strictly positive types*, Theoret. Comput. Sci. **342** (2005) 3–27.

[M4-5]: https://github.com/ualib/agda-algebras/issues/338
[M4-5a]: https://github.com/ualib/agda-algebras/issues/339
[M4-5b]: https://github.com/ualib/agda-algebras/issues/340
[M4-5c]: https://github.com/ualib/agda-algebras/issues/341
[M4-5d]: https://github.com/ualib/agda-algebras/issues/342
[M4-16]: https://github.com/ualib/agda-algebras/issues/403
