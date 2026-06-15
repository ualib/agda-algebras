---
layout: default
file: "src/Classical/Structures/CommutativeSemigroup.lagda.md"
title: "Classical.Structures.CommutativeSemigroup module"
date: "2026-05-24"
author: "the agda-algebras development team"
---

### Commutative Semigroups

This is the [Classical.Structures.CommutativeSemigroup][] module of the [Agda Universal Algebra Library][].

A commutative semigroup is `Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ Th-CommutativeSemigroup` over
`Sig-Magma`.  It is the first *equation-only extension* of an equation-bearing
predecessor, exercising the ADR-002 v2 §5 rule that the forgetful projection of such
an extension is a pure theory-**reindex** (the algebra is kept; the satisfaction proof
is restricted to the predecessor's equations), so the predecessor's `<Weaker>-Op`
accessors inherit through it unchanged.  `CommutativeSemigroup-Op` adds only the new
curried `comm-law`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.CommutativeSemigroup where

open import Agda.Primitive                          using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -----------------------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Level                                  using ( Level ; _⊔_ ; suc )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( _≡_ )

-- Imports from the Agda Universal Algebra Library --------------------------------
open import Classical.Signatures.Magma               using  ( Sig-Magma )
open import Classical.Structures.Magma               using  ( opsToMagma )
open import Classical.Structures.Semigroup           using  ( Semigroup ; module Semigroup-Op )
open import Classical.Theories.Semigroup             using  ( Th-Semigroup ; assoc )
open import Classical.Theories.CommutativeSemigroup  using  ( Eq-CommutativeSemigroup
                                                            ; Th-CommutativeSemigroup ; comm )
                                                     renaming ( assoc to assocᶜ )
open import Overture.Terms {𝑆 = Sig-Magma}           using  (Term ; ℊ )
open import Setoid.Algebras.Basic {𝑆 = Sig-Magma}    using  ( Algebra ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Varieties.EquationalLogic {𝑆 = Sig-Magma} using ( _⊧_≈_ )

private variable α ρ : Level
```

#### Satisfaction predicate and the type

```agda
infix 4 _⊨ᶜˢᵍ_
_⊨ᶜˢᵍ_ : (𝑨 : Algebra α ρ) (ℰ : Eq-CommutativeSemigroup → Term (Fin 3) × Term (Fin 3)) → Type (α ⊔ ρ)
𝑨 ⊨ᶜˢᵍ ℰ = ∀ i → 𝑨 ⊧ proj₁ (ℰ i) ≈ proj₂ (ℰ i)

CommutativeSemigroup : (α ρ : Level) → Type (suc α ⊔ suc ρ)
CommutativeSemigroup α ρ = Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ᶜˢᵍ Th-CommutativeSemigroup
```

#### The forgetful projection to semigroups (pure reindex)

The pattern `assoc` is `Eq-Semigroup`'s sole constructor; the applied `assocᶜ` is
`Eq-CommutativeSemigroup`'s (renamed on import).  Both theory entries are
`Associative ∙-Op refl 0F 1F 2F`, hence definitionally equal, so the reindex checks.

```agda
commutativeSemigroup→semigroup : CommutativeSemigroup α ρ → Semigroup α ρ
commutativeSemigroup→semigroup (𝑨 , mod) = 𝑨 , λ { assoc → mod assocᶜ }
```

#### The `CommutativeSemigroup-Op` module

```agda
module CommutativeSemigroup-Op {α ρ : Level} (𝑪 : CommutativeSemigroup α ρ) where
  private 𝑨 = proj₁ 𝑪
  open Setoid 𝔻[ 𝑨 ]

  -- Inherit through the (proj₁-on-algebra) reindex forgetful.
  open Semigroup-Op (commutativeSemigroup→semigroup 𝑪) public
    using ( _∙_ ; ∙-cong ; interp-node ; assoc-law )

  equations : 𝑨 ⊨ᶜˢᵍ Th-CommutativeSemigroup
  equations = proj₂ 𝑪

  comm-law : ∀ x y → x ∙ y ≈ y ∙ x
  comm-law x y = trans (sym (interp-node (ℊ 0F) (ℊ 1F) η))
                       (trans (equations comm η) (interp-node (ℊ 1F) (ℊ 0F) η))
    where η : Fin 3 → 𝕌[ 𝑨 ]
          η = λ { 0F → x ; 1F → y ; 2F → x }
```

#### `eqsToCommutativeSemigroup`

```agda
eqsToCommutativeSemigroup : (A : Type α) (_·_ : A → A → A)
  → (·-assoc : ∀ a b c → (a · b) · c ≡ a · (b · c))
  → (·-comm  : ∀ a b → a · b ≡ b · a)
  → CommutativeSemigroup α α
eqsToCommutativeSemigroup A _·_ ·-assoc ·-comm = opsToMagma _·_ , proof
  where
  proof : opsToMagma _·_ ⊨ᶜˢᵍ Th-CommutativeSemigroup
  proof assocᶜ ρ = ·-assoc (ρ 0F) (ρ 1F) (ρ 2F)
  proof comm   ρ = ·-comm  (ρ 0F) (ρ 1F)
```

--------------------------------------

{% include UALib.Links.md %}
