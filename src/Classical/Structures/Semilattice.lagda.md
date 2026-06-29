---
layout: default
file: "src/Classical/Structures/Semilattice.lagda.md"
title: "Classical.Structures.Semilattice module"
date: "2026-05-27"
author: "the agda-algebras development team"
---

### Semilattices

This is the [Classical.Structures.Semilattice][] module of the [Agda Universal Algebra Library][].

A semilattice is `Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ Th-Semilattice` over `Sig-Magma`.
Equationally, a semilattice is an idempotent commutative semigroup: its theory
extends `Th-CommutativeSemigroup` by the single `idem` equation.  The forgetful
projection `semilattice→commutativeSemigroup` is therefore a pure theory-reindex
(ADR-002 v2 §5): the algebra is kept; only the satisfaction proof is restricted to
the predecessor's `assoc` and `comm` equations.  `Semilattice-Op` inherits `_∙_`,
`∙-cong`, `interp-node`, `assoc-law`, and `comm-law` through the reindex, and adds
the curried `idem-law`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Semilattice where

open import Agda.Primitive                          using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -----------------------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Level                                  using ( Level ; _⊔_ ; suc )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( _≡_ )

-- Imports from the Agda Universal Algebra Library --------------------------------
open import Classical.Signatures.Magma                 using  ( Sig-Magma )
open import Classical.Structures.Magma                 using  ( opsToMagma )
open import Classical.Structures.CommutativeSemigroup  using  ( CommutativeSemigroup
                                                              ; module CommutativeSemigroup-Op )
open import Classical.Theories.CommutativeSemigroup    using  ( assoc ; comm )
open import Classical.Theories.Semilattice             using  ( Eq-Semilattice
                                                              ; Th-Semilattice ; idem )
                                                       renaming ( assoc to assocˢˡ
                                                                ; comm  to commˢˡ )
open import Overture.Terms {𝑆 = Sig-Magma}             using  ( Term ; ℊ )
open import Setoid.Algebras.Basic {𝑆 = Sig-Magma}      using  ( Algebra ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Varieties.EquationalLogic {𝑆 = Sig-Magma} using ( _⊧_≈_ )

private variable α ρ : Level
```

#### Satisfaction predicate and the type

```agda
infix 4 _⊨ˢˡ_
_⊨ˢˡ_ : (𝑨 : Algebra α ρ) (ℰ : Eq-Semilattice → Term (Fin 3) × Term (Fin 3)) → Type (α ⊔ ρ)
𝑨 ⊨ˢˡ ℰ = ∀ i → 𝑨 ⊧ proj₁ (ℰ i) ≈ proj₂ (ℰ i)

Semilattice : (α ρ : Level) → Type (suc α ⊔ suc ρ)
Semilattice α ρ = Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ˢˡ Th-Semilattice
```

#### The forgetful projection to commutative semigroups (pure reindex)

`Th-Semilattice` extends `Th-CommutativeSemigroup` by the single `idem` equation,
over the same `Sig-Magma` signature; the forgetful is the identity on the underlying
algebra and discards the `idem` witness, projecting only `assoc` and `comm`.

```agda
semilattice→commutativeSemigroup : Semilattice α ρ → CommutativeSemigroup α ρ
semilattice→commutativeSemigroup (𝑨 , mod) = 𝑨 , λ { assoc → mod assocˢˡ
                                                   ; comm  → mod commˢˡ }
```

#### The `Semilattice-Op` module

```agda
module Semilattice-Op {α ρ : Level} (𝑺 : Semilattice α ρ) where
  private 𝑨 = proj₁ 𝑺
  open Setoid 𝔻[ 𝑨 ]

  -- Inherit through the (proj₁-on-algebra) reindex forgetful.
  open CommutativeSemigroup-Op (semilattice→commutativeSemigroup 𝑺) public
    using ( _∙_ ; ∙-cong ; interp-node ; assoc-law ; comm-law )

  equations : 𝑨 ⊨ˢˡ Th-Semilattice
  equations = proj₂ 𝑺

  idem-law : ∀ x → x ∙ x ≈ x
  idem-law x = trans (sym (interp-node (ℊ 0F) (ℊ 0F) η)) (equations idem η)
    where η : Fin 3 → 𝕌[ 𝑨 ]
          η = λ { 0F → x ; 1F → x ; 2F → x }
```

#### `eqsToSemilattice`

```agda
eqsToSemilattice : (A : Type α) (_·_ : A → A → A)
  → (·-assoc : ∀ a b c → (a · b) · c ≡ a · (b · c))
  → (·-comm  : ∀ a b → a · b ≡ b · a)
  → (·-idem  : ∀ a → a · a ≡ a)
  → Semilattice α α
eqsToSemilattice A _·_ ·-assoc ·-comm ·-idem = opsToMagma _·_ , proof
  where
  proof : opsToMagma _·_ ⊨ˢˡ Th-Semilattice
  proof assocˢˡ ρ = ·-assoc (ρ 0F) (ρ 1F) (ρ 2F)
  proof commˢˡ  ρ = ·-comm  (ρ 0F) (ρ 1F)
  proof idem    ρ = ·-idem  (ρ 0F)
```
