<!-- File: docs/notes/milestone-signature-functors.md -->

# M4-5 design note: signatures as functors — reducts, expansions, and interpretability

This note is the design reference for milestone [M4-5][] (#338) and its subissues #339–#345.  It records the mathematical core, the dependency chain between the subissues, the de-risking spikes, the decisions settled so far, and the open questions.  Architectural decisions that need to survive the milestone are promoted to ADRs (currently ADR-006); this note is the working map around them.

## The observation that motivates the milestone

The `Setoid/` foundation already *is* a polynomial-functor formalization; it just does not say so.  Concretely:

+  `Signature 𝓞 𝓥 = Σ[ F ∈ Type 𝓞 ] (F → Type 𝓥)` is a **container** `(OperationSymbolsOf ▷ ArityOf)`.
+  `⟨ 𝑆 ⟩` (the functor `Setoid.Algebras.Basic` applies to a domain) is the **polynomial functor** `P_𝑆` of that container, lifted to setoids.
+  `Interp : Func (⟨ 𝑆 ⟩ Domain) Domain` is the **structure map** `P_𝑆(A) → A` of an algebra.
+  `Term X` is the **initial algebra** of `A ↦ X ⊎ P_𝑆(A)` — the free `P_𝑆`-algebra on `X`.

[M4-5][] makes this explicit and reusable.  Doing so also gives the frozen `Legacy/Base/Categories` and `Legacy/Base/Adjunction` orphans a principled, `--safe`, funext-free home in the canonical tree.

## Mathematical core

+  **Signatures and their morphisms form a category `Sig`.**  A morphism `𝑆₁ → 𝑆₂` is a container morphism `(ι , κ)`: `ι` maps operation symbols forwards, `κ` maps positions backwards.  This is the Abbott–Altenkirch–Ghani category of containers, restricted to the algebraic case (no relation symbols).
+  **`⟨_⟩` is a functor**, covariant in the carrier; a signature morphism induces a natural transformation `P_{𝑆₁} ⟹ P_{𝑆₂}` between the polynomial functors.
+  **`reduct` is precomposition with that natural transformation.**  For `φ : 𝑆₁ → 𝑆₂`, `reduct φ : Alg(𝑆₂) → Alg(𝑆₁)` sends an algebra's structure map `P_{𝑆₂}(A) → A` to `P_{𝑆₁}(A) → P_{𝑆₂}(A) → A`.  `reduct` is a (contravariant-on-`Sig`, covariant-on-algebras) functor.
+  **Free expansion is left adjoint to reduct**, `F ⊣ reduct`, along signature inclusions; along inclusions that *add equations* the left adjoint needs a quotient (a setoid quotient now, a cubical HIT later).
+  **`Term` is a monad**; the fold (initiality) is natural, and reduct-invariance of satisfaction falls out as a corollary.
+  **Theory interpretations** are signature morphisms into *derived* operations (terms) that preserve equations; they organize varieties into the interpretability quasi-order, and Maltsev conditions are interpretations of specific theories.
+  **Reduct classes of varieties are prevarieties** — closed under `S` and `P`, not in general under `H`.

## Subissue chain

The dependency order is `a → b → c → {d, e}`, with `e` gating `f` and `c` gating `g`.

+  **[M4-5a][] — Category of signature morphisms (#339).**  *(low risk; done — foundation landed.)*  Package `(ι , κ)` as `SigMorphism`; define identity and composition; prove the category laws; re-express `reduct` to consume a morphism.  See ADR-006 and `Overture.Signatures.Morphisms`.
+  **[M4-5b][] — `⟨_⟩` as a functor; induced natural transformations (#340).**  *(low–medium; done.)*  `⟨ 𝑆 ⟩` is functorial in the carrier (`map`, with `map-id` / `map-∘`); a `SigMorphism` induces a natural transformation `⟦_⟧` of polynomial functors (with its naturality square); and `⟦_⟧` is itself functorial (`⟦id⟧` / `⟦∘⟧`).  Every law is `refl`, pointwise — the foundation-is-a-polynomial-functor observation is now a checked statement.  See `Setoid.Signatures.Functor`.
+  **[M4-5c][] — Reduct as a functor on algebras (#341).**  *(medium; done.)*  A minimal self-contained `Category` / `Functor` vocabulary (ADR-006); `Alg 𝑆` assembled as a category with a **pointwise hom-setoid** (homomorphism equality is pointwise, unlike `Sig`); `reduct φ` packaged as a `Functor (Alg 𝑆₂) (Alg 𝑆₁)` (the morphism action reindexes the `𝑆₂`-`compatible` through `κ`; the laws are `refl`); and `monoid→semigroup` as a forgetful functor (`reductF` of the `Sig-Magma ↪ Sig-Monoid` inclusion, reusing `∙-incl` / `∙-κ`).  See `Setoid.Categories.{Category, Functor, Algebra}` and `Classical.Categories.{Reduct, Forgetful}`.
+  **[M4-5d][] — Free expansion; the `F ⊣ reduct` adjunction (#342).**  *(high / high-value.)*  Construct the left adjoint and prove the universal property.  Distinguish carefully from M3-6's chosen `expand-ε`.
+  **[M4-5e][] — Term monad; naturality of the fold; reduct-invariance of satisfaction (#343).**  *(medium.)*  Establish the monad structure and fold-naturality; derive reduct-invariance of satisfaction, absorbing M3-6's per-structure pivot proofs.
+  **[M4-5f][] — Theory interpretations; Maltsev conditions; the interpretability quasi-order (#344).**  *(research-grade, exploratory.)*  Definition + one or two worked instances + a scope note.  Clone/CSP side (see below).
+  **[M4-5g][] — Reduct classes are prevarieties (#345).**  *(research-grade.)*  Prove the tractable half (`S`, `P`) against `Setoid.Varieties`; document the rest.  Clone/variety side (see below).

## De-risking spikes

+  **Spike A (within [M4-5c][]).**  Supply the morphism action for `monoid→semigroup` only and prove it functorial, before generalizing.
+  **Spike B (within [M4-5d][]).**  Construct the free monoid on a semigroup (adjoin a unit) and prove its universal property against `reduct`; if this single adjunction is clean with setoid quotients, the general theorem is plausible.

## Decisions settled so far

+  **Hom-equality for `Sig` is propositional `_≡_`; the laws are `refl`** (ADR-006, [M4-5a][] spike).  The `Fin n` η-gap of ADR-002 §6 does not bite at the signature level, because the laws compose abstract position maps rather than normalizing `Fin`-pattern lambdas.
+  **The category layer is self-contained — no `agda-categories` dependency** (ADR-006).  The shared `Category` record (introduced where [M4-5c][] first needs it) carries a hom-equality field `_≈_`, instantiated `_≡_` for `Sig` and a pointwise setoid for `Alg`.
+  **Placement.**  Setoid-free signature-level material lives in `Overture` (`Overture.Signatures.Morphisms`); algebra-level material ([M4-5c][] onward) lives in `Setoid/`.  `reduct` stays in its current home and imports the morphism type acyclically.
+  **`reduct` consumes a `SigMorphism`, with a thin `reductBy` wrapper** for the `(ι , κ)`-pair form.  The six call sites route their existing pattern-matched position maps through it; a single generic `embed` (`κ = λ _ → id`) is *not* definable under `--safe`, since the arity match is not definitional for an abstract symbol.  `reduct` is functorial, stated *operation-wise* (carrier definitionally, operations up to `_≡_`) — full algebra equality would need funext for the congruence field.

## Open questions

+  **Adjunction along equation-adding inclusions.**  The left adjoint needs quotients now (setoid quotients), and is a natural place to measure the cubical-HIT payoff later.
+  **Does cubical dissolve the M3-5 binary-node-bridge obstruction?**  That obstruction is an MLTT/`--safe` artifact (the `Fin n` η-gap again).  [M4-5e][] is the place to measure whether the v4.0 cubical port removes it — a concrete, quantifiable portability payoff if so.
+  **Research-track hygiene.**  [M4-5f][]/[M4-5g][] sit on the clone/CSP side of the library and connect forward to M9-2 (infinitary CSP over ω-categorical templates; the Bodirsky–Pinsker program).  They are **not** FLRP work: the interpretability/Maltsev/clone material and the Finite Lattice Representation Problem are kept in separate research tracks, and conflating them is an error to flag in review.

## Relationship to other work

+  **The `Legacy/Base` orphans.**  `Legacy/Base/Categories/Functors` and `Legacy/Base/Adjunction/{Closure,Residuation,Galois}` are the frozen, funext-postulating prototypes of this material; [M4-5][] is their principled replacement in the canonical, `--safe` tree.  They are reference-only and are not imported.
+  **M3-6.**  [M4-5e][] generalizes M3-6's per-structure satisfaction-pivot proofs into one reduct-invariance corollary; the free expansion of [M4-5d][] must be kept distinct from the chosen `expand-ε` of [M3-6][].
+  **ADR-002.**  The classical forgetful projections that [M4-5c][] upgrades to functors are exactly the reducts ADR-002 §5 introduced.

[M4-5]: https://github.com/ualib/agda-algebras/issues/338
[M4-5a]: https://github.com/ualib/agda-algebras/issues/339
[M4-5b]: https://github.com/ualib/agda-algebras/issues/340
[M4-5c]: https://github.com/ualib/agda-algebras/issues/341
[M4-5d]: https://github.com/ualib/agda-algebras/issues/342
[M4-5e]: https://github.com/ualib/agda-algebras/issues/343
[M4-5f]: https://github.com/ualib/agda-algebras/issues/344
[M4-5g]: https://github.com/ualib/agda-algebras/issues/345
