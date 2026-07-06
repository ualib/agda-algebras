---
layout: default
file: "src/Setoid/Congruences/Monolith.lagda.md"
title: "Setoid.Congruences.Monolith module (The Agda Universal Algebra Library)"
date: "2026-06-20"
author: "the agda-algebras development team"
---

### Monoliths and subdirectly irreducible algebras

This is the [Setoid.Congruences.Monolith][] module of the [Agda Universal Algebra Library][].

[Setoid.Congruences.CompleteLattice][] organized the congruences of an algebra into a
complete lattice with bottom `0ᴬ` (the diagonal) and top `1ᴬ`.  This module isolates
the order-theoretic property at the heart of *subdirect irreducibility*: an algebra is
**subdirectly irreducible** (SI) when it is nontrivial and `0ᴬ` has a unique cover — a
**monolith**, the least congruence strictly above the diagonal.  Equivalently, `0ᴬ` is
*completely meet-irreducible*: it is not the meet of any family of strictly larger
congruences.

The development here is pure congruence theory and is fully constructive.  We work
throughout with congruences at the algebra's own relation level `ρ`, so the diagonal
`0ᴬ` is the setoid equality `_≈_ : Con 𝑨 ρ` and the monolith (when it exists) is a
`Con 𝑨 ρ`.  The choice-dependent *existence* of subdirect SI-representations —
Birkhoff's subdirect representation theorem — is built on top of this in
[Setoid.Subalgebras.Subdirect][]; nothing here assumes it.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Congruences.Monolith {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive    using () renaming ( Set to Type )
open import Data.Product      using ( _×_ ; _,_ ; Σ-syntax ; ∃-syntax ; proj₁ ; proj₂ )
open import Level             using ( Level ; _⊔_ )
open import Relation.Binary   using ( Setoid ; IsEquivalence ; _⇒_ )
open import Relation.Nullary  using ( ¬_ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Setoid.Algebras.Basic       {𝑆 = 𝑆}  using  ( ov ; Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Congruences.Basic    {𝑆 = 𝑆}  using  ( Con ; mkcon ; _∣≈_ ; reflexive
                                                        ; is-equivalence ; is-compatible )
open import Setoid.Congruences.Lattice  {𝑆 = 𝑆}  using  ( _⊆_ ; _≑_ ; _∧_ )

private variable α ρ ℓ : Level
```
-->

#### Nontriviality and the diagonal

Fix an algebra `𝑨`.  It is **nontrivial** when its carrier has two elements that the
setoid equality keeps apart; the degenerate (one-element) algebras are exactly the
**trivial** ones, on which every two elements are equal.

```agda
module _ (𝑨 : Algebra α ρ) where
  open Setoid 𝔻[ 𝑨 ]  using ( _≈_ )

  -- 𝑨 has two ≈-distinct elements.
  Nontrivial : Type (α ⊔ ρ)
  Nontrivial = ∃[ a ] ∃[ b ] ¬ (a ≈ b)
  -- `∃[ a ] P a`  is shorthand for `Σ[ a ∈ 𝕌[ 𝑨 ] ] P a`

  -- Every two elements of 𝑨 are equal (the one-element, degenerate case).
  Trivial : Type (α ⊔ ρ)
  Trivial = ∀ a b → a ≈ b

  -- A trivial algebra is not nontrivial.
  trivial⇒¬nontrivial : Trivial → ¬ Nontrivial
  trivial⇒¬nontrivial triv (a , b , a≢b) = a≢b (triv a b)
```

A congruence is **below the diagonal** when it relates only `≈`-equal elements; this is
exactly the assertion `θ ≑ 0ᴬ` (since `0ᴬ ⊆ θ` always holds), so its negation is the
right notion of a **nonzero** (strictly-above-`0ᴬ`) congruence.

```agda
  -- θ relates only equal elements, i.e. θ ≑ 0ᴬ.
  BelowDiagonal : Con 𝑨 ℓ → Type (α ⊔ ρ ⊔ ℓ)
  BelowDiagonal ( θ , _ ) = θ ⇒ _≈_

  -- θ is nonzero: it is *not* below the diagonal (it relates some distinct pair).
  Nonzero : Con 𝑨 ℓ → Type (α ⊔ ρ ⊔ ℓ)
  Nonzero θ = ¬ BelowDiagonal θ
```

#### The infinitary meet of a family of congruences

For the completely-meet-irreducible characterization we need the meet (intersection)
of a family of congruences.  This is the same intersection that
[Setoid.Congruences.CompleteLattice][] packages (there as `⋀`, at the absorbing level
`L`); here we take it at the algebra's own relation level `ℓ` for an `ℓ`-small index
`I`, where it stays a `Con 𝑨 ℓ`.

```agda
  ⋂ : {I : Type ℓ} → (I → Con 𝑨 ℓ) → Con 𝑨 ℓ
  ⋂ {I = I} θ = (λ x y → (i : I) → proj₁ (θ i) x y) , mkcon m-refl m-equiv m-comp
    where
    m-refl : ∀ {a₀ a₁} → a₀ ≈ a₁ → (i : I) → proj₁ (θ i) a₀ a₁
    m-refl e i = reflexive (proj₂ (θ i)) e

    open IsEquivalence
    m-equiv : IsEquivalence (λ x y → (i : I) → θ i .proj₁ x y)
    m-equiv .refl   = λ i → (θ i) .proj₂ .is-equivalence .refl
    m-equiv .sym    = λ p i → (θ i) .proj₂ .is-equivalence .sym (p i)
    m-equiv .trans  = λ p q i  → (θ i) .proj₂ .is-equivalence .trans (p i) (q i)

    m-comp : 𝑨 ∣≈ (λ x y → (i : I) → proj₁ (θ i) x y)
    m-comp f h i = is-compatible (proj₂ (θ i)) f (λ k → h k i)

  -- The meet is a lower bound of each family member.
  ⋂-lower : {I : Type ℓ}(θ : I → Con 𝑨 ℓ)(i : I) → ⋂ θ ⊆ θ i
  ⋂-lower θ i p = p i
```

#### Monoliths

A **monolith** of `𝑨` is a least nonzero congruence: it is itself nonzero, and it is
contained in every nonzero congruence.  (Working at the algebra's relation level `ρ`,
so the diagonal and the monolith are `Con 𝑨 ρ`.)

```agda
  record IsMonolith (μ : Con 𝑨 ρ) : Type (α ⊔ ov ρ) where
    field
      mono-nonzero : Nonzero μ
      mono-least   : (θ : Con 𝑨 ρ) → Nonzero θ → μ ⊆ θ

  open IsMonolith public

  HasMonolith : Type (α ⊔ ov ρ)
  HasMonolith = Σ[ μ ∈ Con 𝑨 ρ ] IsMonolith μ
```

The monolith, when it exists, is unique up to mutual containment `≑`: two least nonzero
congruences are each below the other.

```agda
  monolith-unique : (m m′ : HasMonolith) → proj₁ m ≑ proj₁ m′
  monolith-unique (μ , mono) (μ′ , mono′) =
    mono-least mono  μ′ (mono-nonzero mono′) , mono-least mono′ μ  (mono-nonzero mono)
```

#### Subdirect irreducibility

An algebra is **subdirectly irreducible** when it is nontrivial and has a monolith.
(The role of SI algebras in subdirect *representations* — Birkhoff's theorem that every
algebra is a subdirect product of SI algebras — is developed in
[Setoid.Subalgebras.Subdirect][].)

```agda
  IsSubdirectlyIrreducible : Type (α ⊔ ov ρ)
  IsSubdirectlyIrreducible = Nontrivial × HasMonolith

  -- An SI algebra is nontrivial; a trivial algebra is not SI.
  si⇒nontrivial : IsSubdirectlyIrreducible → Nontrivial
  si⇒nontrivial = proj₁

  trivial⇒¬si : Trivial → ¬ IsSubdirectlyIrreducible
  trivial⇒¬si triv si = trivial⇒¬nontrivial triv (si⇒nontrivial si)
```

#### The monolith characterization

The substantive fact is that having a monolith makes `0ᴬ` **completely meet-irreducible**:
whenever a family of congruences meets to the diagonal, some member is already the
diagonal.  Constructively we state and prove the contrapositive — *if every member of a
family is nonzero, then so is the meet* — which is the form actually used downstream and
avoids extracting a witnessing index from a negated existential.  As with the monolith,
the family ranges over congruences at the algebra's relation level `ρ`.

```agda
  -- 0ᴬ is completely meet-irreducible (contrapositive form).
  CompletelyMeetIrreducible : Type (α ⊔ ov ρ)
  CompletelyMeetIrreducible =
    {I : Type ρ}(θ : I → Con 𝑨 ρ) → (∀ i → Nonzero (θ i)) → Nonzero (⋂ θ)
```

The proof: the monolith `μ` is below every nonzero `θ i`, hence below the meet; if the
meet were below the diagonal, so would `μ` be, contradicting `Nonzero μ`.

```agda
  monolith⇒cmi : HasMonolith → CompletelyMeetIrreducible
  monolith⇒cmi (μ , mono) θ all-nonzero ⋂θ⊆Δ = mono-nonzero mono μ⊆Δ
    where
    μ⊆θ : ∀ i → μ ⊆ θ i
    μ⊆θ i = mono-least mono (θ i) (all-nonzero i)
    μ⊆⋂ : μ ⊆ ⋂ θ
    μ⊆⋂ p i = μ⊆θ i p
    μ⊆Δ : BelowDiagonal μ
    μ⊆Δ p = ⋂θ⊆Δ (μ⊆⋂ p)
```

```agda
  -- The binary instance: the meet of two nonzero congruences is nonzero, i.e. `0ᴬ`
  -- is meet-irreducible.  This is the "directly-indecomposable-adjacent" fact: a
  -- monolithic algebra cannot have two nonzero congruences with diagonal meet.
  monolith⇒∧-irreducible :
    HasMonolith → (θ φ : Con 𝑨 ρ) → Nonzero θ → Nonzero φ → Nonzero (θ ∧ φ)
  monolith⇒∧-irreducible (μ , mono) θ φ nzθ nzφ θ∧φ⊆Δ = mono-nonzero mono μ⊆Δ
    where
    μ⊆θ : μ ⊆ θ
    μ⊆θ = mono-least mono θ nzθ
    μ⊆φ : μ ⊆ φ
    μ⊆φ = mono-least mono φ nzφ
    μ⊆Δ : BelowDiagonal μ
    μ⊆Δ p = θ∧φ⊆Δ (μ⊆θ p , μ⊆φ p)
```
