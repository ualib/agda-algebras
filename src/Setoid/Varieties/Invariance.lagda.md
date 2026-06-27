---
layout: default
file: "src/Setoid/Varieties/Invariance.lagda.md"
title: "Setoid.Varieties.Invariance module"
date: "2026-06-12"
author: "the agda-algebras development team"
---

### Reduct-invariance of satisfaction

This is the [Setoid.Varieties.Invariance][] module of the [Agda Universal Algebra Library][].

This module proves the *reduct-invariance of satisfaction*, which is the primary
pay-off of expressing the reduct as a functor.

For a signature morphism `φ : 𝑆₁ → 𝑆₂`, an `𝑆₂`-algebra `𝑨`, and
`𝑆₁`-terms `s , t`, we have

    reduct φ 𝑨 ⊧ s ≈ t   if and only if   𝑨 ⊧ φ ✶ s ≈ φ ✶ t.

In words: to check an equation against the *poorer* view of `𝑨` (the reduct, which
sees only the `𝑆₁`-operations) is the same as checking the *translated* equation
against `𝑨` itself.

Model theorists know this as (the equational case of) the **satisfaction condition**
of institutions,[^1] and universal algebraists use it tacitly every time we say
"a monoid satisfies the semigroup laws."

##### Why this is naturality of the fold

Nothing about the theorem is specific to satisfaction; the satisfaction statement is
the shadow of one commuting triangle of interpretation maps.  Fix an environment
`η : X → 𝕌[ 𝑨 ]` (note `𝑨` and `reduct φ 𝑨` have the *same* carrier, so one
environment serves both, and `φ ✶_` fixes variables, so no translation of `η` is
needed).

Evaluation of `𝑆₁`-terms in the reduct, and of `𝑆₂`-terms in `𝑨`, fit around the term
translation.

```text
                  φ ✶_
        Term₁ X ────────→ Term₂ X

             ╲             │  ⟦_⟧ in 𝑨
    ⟦_⟧ in     ╲           │  (the 𝑆₂-fold)
    reduct φ 𝑨   ╲         │
                   ╲       |
                    ╲      |
                     ╲     |
                      ↘    ↓

                      𝕌[ 𝑨 ]
```

`reduct-interp` below proves this triangle commutes, by structural induction on the
term.  Both routes are *folds* — unique homomorphic extensions out of term algebras
— and the triangle is precisely the naturality of the fold with respect to the
natural transformation `⟦ φ ⟧ : ⟨ 𝑆₁ ⟩ ⟹ ⟨ 𝑆₂ ⟩` induced by `φ` (M4-5b,
[Setoid.Signatures.Functor][]): unwinding the `node` case of the proof, the
inductive step is exactly "precompose with `⟦ φ ⟧`'s component, then interpret" —
which is the defining clause of [`reduct`][Setoid.Algebras.Reduct].  Once the
triangle commutes, both invariance directions are two-line equational
rearrangements: an equation `⟦s⟧ ≈ ⟦t⟧` holds on one side of the triangle iff it
holds on the other.

The companion naturality in the *algebra* argument — fix the signature, vary the
algebra along a homomorphism — is `free-lift-natural` / `comm-hom-term`
([Setoid.Terms.Properties][], [Setoid.Terms.Operations][]).  The two naturalities
together say the interpretation pairing `(𝑨 , t) ↦ ⟦ t ⟧ᴬ` is functorial in both
coordinates, which is the full content of "`⟦_⟧` is the unique fold."

##### What this absorbs, and the M3-5 measurement

M3-6 discharged theory obligations for reduct-derived forgetfuls by hand: the
`Th-Semigroup` obligation inside `monoid→semigroup`
([Classical.Structures.Monoid][]) pivots through curried associativity using
per-signature `interp-node` bridges, each paying the `Fin n` η-gap (ADR-002 §1, the
M3-5 finding) once.  `⊧-reduct` replaces that pattern: the general lemma is proved
*once*, by structural induction over abstract positions, and — this is the
measurement the issue asks to record — **the M3-5 binary-node-bridge obstruction
does not appear at the functorial level**.  No clause here matches `refl` against a
neutral `ArityOf 𝑆 f ≡ Fin 2`, no `interp-node` family is needed, and no `Fin`
η-bridge is paid: the induction never compares a concrete `Fin`-pattern lambda
against an abstract tuple.  What residue remains is per-*theory*, not per-signature:
a concrete theory written with `pair`-style `Fin`-lambdas must be aligned with its
translation up to the term equality `_≐_` (a finite, mechanical pattern-match; see
the demonstration in [Classical.Categories.Forgetful][]) — and that alignment is
`≐`-provable where a propositional `≡` would be funext-blocked.  Conclusion: the
obstruction dissolves functorially; only its benign, provable shadow survives, in
the concrete theories themselves.

This module lives in `Setoid.Varieties`: reduct-invariance of satisfaction is general
universal algebra, and its object map [`reduct`][Setoid.Algebras.Reduct] is itself a
`Setoid/` construction (both relocated from `Classical/` by
[ADR-006](../../docs/adr/006-signature-morphism-category.md), M4-16).  It opens the
two-signature `Setoid/Varieties/` area that M4-5g (reduct classes of varieties) extends.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Varieties.Invariance where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive                 using () renaming ( Set to Type )
open import Data.Product                   using ( _,_ )
open import Function                       using ( Func )
open import Level                          using ( Level )
open import Relation.Binary                using ( Setoid )

open import Relation.Binary.PropositionalEquality using (refl) -- as ≡

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Signatures            using ( 𝓞 ; 𝓥 ; Signature )
open import Overture.Signatures.Morphisms  using ( SigMorphism ; κ )
open import Overture.Terms                 using ( Term ; ℊ ; node )
open import Overture.Terms.Translation     using ( _✶_ )
open import Setoid.Algebras.Basic          using ( Algebra ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Algebras.Reduct         using ( reduct )

open import Setoid.Terms.Basic          using (module Environment) --        as TermsBasic
import Setoid.Varieties.EquationalLogic    as EqLogic

open Algebra using ( Interp )
open Func using ( cong ) renaming ( to to _⟨$⟩_ )

private variable
  α ρ χ : Level
  X : Type χ
```

#### Naturality of the fold along a signature morphism

Everything below is parameterized by the morphism `φ` and the `𝑆₂`-algebra `𝑨`.  The
two `Environment` instances interpret `𝑆₁`-terms in `reduct φ 𝑨` and `𝑆₂`-terms in
`𝑨`; the two `_⊧_≈_` instances are the corresponding satisfaction relations.

```agda
module _ {𝑆₁ 𝑆₂ : Signature 𝓞 𝓥} (φ : SigMorphism 𝑆₁ 𝑆₂) (𝑨 : Algebra {𝑆 = 𝑆₂} α ρ) where
  open Environment {𝑆 = 𝑆₁} (reduct φ 𝑨) using () renaming ( ⟦_⟧ to ⟦_⟧₁ )
  open Environment {𝑆 = 𝑆₂} 𝑨 using () renaming ( ⟦_⟧ to ⟦_⟧₂ )
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ) renaming (refl to ≈refl; sym to ≈sym ; trans to ≈trans )
  open EqLogic {𝑆 = 𝑆₁} using () renaming ( _⊧_≈_ to _⊧₁_≈_ )
  open EqLogic {𝑆 = 𝑆₂} using () renaming ( _⊧_≈_ to _⊧₂_≈_ )
```

The commuting triangle: interpreting an `𝑆₁`-term in the reduct is interpreting its
translation in `𝑨`, under any environment.  At a leaf both sides look up the
variable.  At a node, the reduct's interpretation *is* "apply the interpretation
in `𝑨` of `ι φ f` to the `κ φ f`-reindexed arguments" — definitionally, by the defining
clause of `reduct` — and the translation's `node` clause performs the same
reindexing syntactically, so the two sides agree position by position, by the
inductive hypothesis at the reindexed subterms.  Note what does *not* happen: no
arity is ever compared to a concrete `Fin n`, so the without-K unifier is never
asked to invert anything.

```agda
  reduct-interp : (t : Term X) (η : X → 𝕌[ 𝑨 ]) → ⟦ t ⟧₁ ⟨$⟩ η ≈ ⟦ φ ✶ t ⟧₂ ⟨$⟩ η
  reduct-interp (ℊ x) η = ≈refl
  reduct-interp (node f ts) η =
    cong (Interp 𝑨) (refl , λ j → reduct-interp (ts (κ φ f j)) η)
```

#### The satisfaction condition

Satisfaction is the interpretation triangle quantified over environments, so each
direction of the invariance is a `trans`-sandwich of the triangle around the given
satisfaction proof.  Recall `𝑨 ⊧ p ≈ q` unfolds to "for every environment `η`,
`⟦ p ⟧ η ≈ ⟦ q ⟧ η`"; environments transfer across the two sides on the nose
because the carrier of the reduct *is* the carrier of `𝑨` and translation fixes
variables.

`⊧-reduct` is the direction that discharges theory obligations of reduct-derived
forgetful functors (a monoid's associativity, translated, *is* the semigroup
associativity its reduct must satisfy); `⊧-expand` is the converse, the direction
used when transporting equational facts from a reduct up to its expansion.

```agda
  ⊧-reduct : {s t : Term X} → 𝑨 ⊧₂ (φ ✶ s) ≈ (φ ✶ t) → reduct φ 𝑨 ⊧₁ s ≈ t
  ⊧-reduct {s = s} {t} A⊧ η =
    ≈trans (reduct-interp s η) (≈trans (A⊧ η) (≈sym (reduct-interp t η)))

  ⊧-expand : {s t : Term X} → reduct φ 𝑨 ⊧₁ s ≈ t → 𝑨 ⊧₂ φ ✶ s ≈ φ ✶ t
  ⊧-expand {s = s} {t} R⊧ η =
    ≈trans (≈sym (reduct-interp s η)) (≈trans (R⊧ η) (reduct-interp t η))
```

Together the two directions are the biconditional promised at the top.  They are
deliberately kept as two one-directional lemmas rather than packaged into a single
`iff` record: every consumer uses exactly one direction, and the unpacked forms
compose directly with the satisfaction proofs the `Classical` theories carry.

--------------------------------------

[^1]: Goguen and Burstall's slogan is, "Truth is invariant under change of notation."
