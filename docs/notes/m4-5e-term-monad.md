<!-- File: docs/notes/m4-5e-term-monad.md -->

# M4-5e design note: the term monad, fold naturality, and the two measurements

This note records the outcome of [M4-5e][] (#343): the term-monad laws, the naturality of the fold in both of its arguments, the reduct-invariance-of-satisfaction theorem, and the two findings the issue asked to be measured and recorded — the universe-level status of the term monad, and the fate of the M3-5 binary-node-bridge obstruction at the functorial level.  Read it with the milestone map [`milestone-signature-functors.md`](milestone-signature-functors.md) and the session handoff [`m4-5d-handoff.md`](m4-5d-handoff.md).

## What landed

+  `Setoid.Categories.NaturalTransformation` — the `NaturalTransformation` record (component family + naturality square), the third rung of the ADR-006 vocabulary, as deferred to this issue by the footnote in `Setoid.Categories.Adjunction`.
+  `Setoid.Categories.Functor` — `idF` and `_∘F_` (identity and composition of functors), needed to *type* `Id ⟹ T` and `T ∘ T ⟹ T`.
+  `Setoid.Categories.Monad` — the `Monad` record, built on `NaturalTransformation` for its `unit` and `mult` fields with the three laws componentwise (the `Adjunction` convention); and `adjunction→monad`, the general theorem that every adjunction induces a monad on the left adjoint's domain.
+  `Setoid.Categories.Adjunction` — derived `unitNT` / `counitNT` views; the componentwise fields remain the canonical form (per the M4-5d note's follow-up, the re-packaging was *not* made canonical: instances supply componentwise data pointwise, and the bundled views are free).
+  `Classical.Categories.AdjoinUnit` — `adjoinUnitMonad : Monad (Semigroups α ρ)`, the M4-5d adjunction run through `adjunction→monad`: the "Maybe monad on semigroups," a one-liner because the triangle identities already did the work.
+  `Overture.Terms.Translation` — `φ ✶ t`, the setoid-free translation of terms along a `SigMorphism` (relabel symbols by `ι`, reindex positions by `κ`, recurse); the free extension of M4-5b's `⟦ φ ⟧` from single applications to terms.
+  `Setoid.Terms.Monad` — the term-monad laws in Kleisli form (`[]-unitˡ` strict by `refl` with a `-ptw` corollary; `[]-unitʳ` and `[]-assoc` by induction up to `_≐_`; `[]-cong`), substitution composition `_⊙ˢ_`, the Kleisli category `TermKleisli χ : Category (suc χ) (ov χ) (ov χ)` whose three category laws *are* the three monad laws, and the heterogeneous-level `join` with its definitional unit law.
+  `Setoid.Terms.Translation` — the `_≐_`-level laws of `_✶_`: congruence (`✶-cong`, packaged as `✶-func`), functoriality (`✶-id`, `✶-∘`), and the monad-morphism square (`✶-sub`: translation commutes with substitution).
+  `Setoid.Terms.Properties` — `free-lift-natural`: naturality of the fold in the algebra, a one-liner by `free-unique` (both triangle legs agree on generators); together with the existing `comm-hom-term` / `free-lift-interp` / `substitution` this completes the carrier-direction naturality inventory.
+  `Classical.Varieties.Invariance` — the payoff: `reduct-interp` (the fold-naturality triangle along `φ`: interpreting an `𝑆₁`-term in `reduct φ 𝑨` is interpreting its translation in `𝑨`) and the satisfaction condition `⊧-reduct` / `⊧-expand` (`reduct φ 𝑨 ⊧ s ≈ t` iff `𝑨 ⊧ φ ✶ s ≈ φ ✶ t`).  This opens the `Classical/Varieties/` area that M4-5g will extend.
+  `Classical.Categories.Forgetful` — the regression demonstration: `Th-Semigroup-via-invariance` re-derives the Monoid forgetful's theory obligation from `⊧-reduct` plus two four-line `_≐_` bridges; the bespoke M3-6 proof (`thm` in `Classical.Structures.Monoid`) is kept, per the issue's instruction.

## Finding 1: the term monad is a relative monad — the Kleisli form is forced

The issue asked to establish `Term 𝑆 : Setoid → Setoid` as a monad.  The laws are established, but the phrase "endofunctor on setoids" is unavailable in a predicative, non-cumulative universe hierarchy, and this is worth recording precisely because it is *not* one of the library's usual `--safe`/η artifacts:

+  `Term X : Type (ov χ)` for `X : Type χ`, where `ov χ = 𝓞 ⊔ 𝓥 ⊔ suc χ`; the `suc` is forced because terms mix leaves from `X` with operation symbols from `Type 𝓞`.  Levels strictly grow, `ov (ov χ) ≠ ov χ`, so `Term` is an endofunctor of no fixed-level category, `η : Id ⟹ Term` does not type-check at any level, and the `Monad` record cannot be instantiated by `Term` — there is nothing to weaken or quotient around this.
+  What `Term` *is*, exactly, is a **relative monad** (Altenkirch–Chapman–Uustalu) over the universe-lifting inclusion `Type χ → Type (ov χ)`, and a relative monad's canonical presentation is the **Kleisli (extension) form**: unit `ℊ` plus substitution `_[ σ ]` as the extension operation.  That form never mentions `T ∘ T`, so it states and proves cleanly at heterogeneous levels; the three laws are exactly the issue's task list (left unit, right unit, associativity of substitution).
+  The categorical packaging that *is* level-correct is the **Kleisli category**: objects `Type χ`, arrows `X ⟶ Y` the substitutions `Sub Y X`, identity `ℊ`, composition `_⊙ˢ_`, hom-equality pointwise `_≐_`.  `TermKleisli χ` is a bona fide `Category` instance and its three laws are discharged by the three monad laws — the monad-ness of `Term` is a checked categorical statement after all, just not via the endofunctor record.
+  The abstract `Monad` record is *not* left uninhabited: `adjunction→monad` inhabits it generically, and `adjoinUnitMonad` concretely.  The division of labor is deliberate — `Monad` is the right vocabulary for fixed-level monads (those arising from adjunctions between the bundle categories), the Kleisli form for the level-raising syntactic monad.
+  **Cubical will not change this.**  Unlike the η-gap items, the level obstruction is a fact about predicativity, not about identity types; the v4.0 port should expect to keep the Kleisli presentation.  (`--cumulativity` could mask the symptom but is out of scope for the `--safe --cubical-compatible` regime and would not make `ov` idempotent anyway.)

A small wart surfaced while placing the laws: `Setoid.Terms.Basic` defines `Sub` / `_[_]` and `Setoid.Terms.Operations` independently defines the synonyms `Substerm` / `_[_]t`.  `Sub` / `_[_]` is the canonical pair (it is what `Setoid.Varieties.SoundAndComplete` consumes, and now what the monad laws govern); reconciling the duplicate is a deprecation-cycle cleanup for a later housekeeping issue, not done here.

## Finding 2: the M3-5 node-bridge obstruction dissolves at the functorial level

The M3-5 finding (ADR-002 §1) was that the binary node-bridge `⟦ node f (pair s t) ⟧ ⟨$⟩ η ≈ ⟦ s ⟧ ⟨$⟩ η ∙ ⟦ t ⟧ ⟨$⟩ η` cannot be stated generically — `node f (pair s t)` type-checks only when `ArityOf 𝑆 f` reduces to `Fin 2`, and the generic statement would need a `refl`-match on a *neutral* `ArityOf 𝑆 f ≡ Fin 2`, which the without-K unifier rejects — so every structure hand-rolls an `interp-nodeₙ` family.  The issue asked whether this survives at the functorial level.  Measured answer: **it does not survive; only a benign, provable shadow remains, and it moves from the signatures to the theories.**

+  The general layer is completely obstruction-free.  `_✶_`, its laws, `reduct-interp`, and `⊧-reduct` / `⊧-expand` are structural inductions over *abstract* positions; no clause compares an arity to a concrete `Fin n`, no `interp-node` family appears, no `Fin` η-bridge is paid, and the without-K unifier is never asked to invert anything.  This is the same mechanism the M4-5a/b laws benefited from (abstract position maps compose; only concrete `Fin`-pattern lambdas η-fail), now confirmed at the satisfaction level.
+  The shadow: a *concrete theory* written with `pair`-style `Fin`-lambdas must be aligned with the `✶`-image of another concrete theory's terms before the general lemma applies — `magma↪monoid ✶ (semigroup assoc-lhs)` and the monoid `assoc`-lhs agree pointwise-recursively but not definitionally (the translation rebuilds position functions through `κ`).  The alignment is a finite `_≐_` pattern-match (`bridgeˡ` / `bridgeʳ` in `Classical.Categories.Forgetful`, four lines each), provable exactly because `_≐_` is the pointwise-recursive equality — the corresponding `_≡_` statement is funext-blocked.  One residue per theory-equation, not per signature, and no unifier involvement.
+  Cubical-port datum: with funext (or with theories restated via `≐`-insensitive builders), the bridges become transports of `refl`; the general layer needs no change at all.  So M4-5e's column in the v4.0 cost/benefit table reads: *nothing to port but the bridges, and the bridges erase*.
+  The implicit-pinning discipline of the handoff recurs in exactly one place: `⊧-reduct`'s equation sides must be pinned at the use site (`{s = …} {t = …}`), because `s` is not recoverable from `φ ✶ s` or `⟦ s ⟧` (both recurse on `s`).  Same root cause as the M4-5b/c/d sightings; now confirmed at a fourth site.

## Inventory: where each naturality statement lives

The issue's "fold naturality" splits along the two arguments of the interpretation pairing `(𝑨 , t) ↦ ⟦ t ⟧ᴬ`, and the formal artifacts are distributed as follows:

+  **Naturality in the algebra** (signature fixed, algebra varies along `h : 𝑨 ⟶ 𝑩`): `free-lift-natural` (`Setoid.Terms.Properties`, new, by `free-unique`), `comm-hom-term` (`Setoid.Terms.Operations`, pre-existing, environment form), with `free-lift-interp` mediating and `substitution` (`Setoid.Terms.Basic`) covering the Kleisli/Eilenberg–Moore interaction.
+  **Naturality in the signature** (algebra fixed, signature varies along `φ : 𝑆₁ → 𝑆₂`): `reduct-interp` (`Classical.Varieties.Invariance`, new), with satisfaction-invariance as the quantified corollary.
+  **Naturality of the translation itself** (the monad-morphism square): `✶-sub` (`Setoid.Terms.Translation`, new), which M4-5f's theory interpretations will need for composability.

## Follow-ups

+  M4-5f (#344): theory interpretations generalize `_✶_` by sending symbols to *derived* terms; `✶-sub` is the composability law, and `Classical.Varieties.Invariance` the template for the satisfaction side.
+  M4-5g (#345): `Classical/Varieties/` now exists; the prevariety results extend it against `Setoid.Varieties`.
+  Optional cleanups, deliberately not done here: reconcile `Sub`/`_[_]` with `Substerm`/`_[_]t` (deprecation cycle); a `⊧-respects-≐` convenience lemma in `Setoid.Varieties` if a second consumer of the bridge pattern appears; vertical/horizontal composition for `NaturalTransformation` when a second consumer needs them.

[M4-5e]: https://github.com/ualib/agda-algebras/issues/343
