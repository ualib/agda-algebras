---
layout: default
file: "src/Classical/Bundles/CommutativeSemigroup.lagda.md"
title: "Classical.Bundles.CommutativeSemigroup module"
date: "2026-05-24"
author: "the agda-algebras development team"
---

### Bundle bridge for commutative semigroups

This is the [Classical.Bundles.CommutativeSemigroup][] module of the [Agda Universal Algebra Library][].

Mirror of the Semigroup bridge with the added `comm` field; over `Sig-Magma`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Bundles.CommutativeSemigroup where

-- Imports from the Agda Standard Library -----------------------------------------
open import Algebra.Bundles     using () renaming (  CommutativeSemigroup
                                                     to stdlib-CommutativeSemigroup )
open import Data.Fin.Patterns   using ( 0F ; 1F ; 2F )
open import Data.Product        using ( _,_ ; proj₁ )
open import Function            using ( Func )
open import Level               using ( Level )
open import Relation.Binary     using ( Setoid )
import Relation.Binary.PropositionalEquality as ≡
open Func renaming ( to to _⟨$⟩_ )

-- Imports from the Agda Universal Algebra Library --------------------------------
open import Classical.Signatures.Magma                 using  ( ∙-Op ; Sig-Magma )
open import Classical.Structures.CommutativeSemigroup  using  ( CommutativeSemigroup
                                                              ; module CommutativeSemigroup-Op )
open import Classical.Theories.CommutativeSemigroup    using  ( assoc ; comm )
open import Setoid.Algebras.Basic {𝑆 = Sig-Magma}      using  ( Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Signatures                          using ( ⟨_⟩ )

private variable α ρ : Level

⟨_⟩ᶜˢᵍ : CommutativeSemigroup α ρ → stdlib-CommutativeSemigroup α ρ
⟨ 𝑪 ⟩ᶜˢᵍ = record
  { Carrier = 𝕌[ proj₁ 𝑪 ]
  ; _≈_     = _≈_
  ; _∙_     = _∙_
  ; isCommutativeSemigroup = record
      { isSemigroup = record
          { isMagma = record { isEquivalence = isEquivalence ; ∙-cong = ∙-cong }
          ; assoc   = assoc-law
          }
      ; comm = comm-law
      }
  }
  where
  open CommutativeSemigroup-Op 𝑪
  open Setoid 𝔻[ proj₁ 𝑪 ]

⟪_⟫ᶜˢᵍ : stdlib-CommutativeSemigroup α ρ → CommutativeSemigroup α ρ
⟪ S ⟫ᶜˢᵍ = 𝑨 , λ { assoc ρ → S-assoc (ρ 0F) (ρ 1F) (ρ 2F)
                ; comm  ρ → S-comm  (ρ 0F) (ρ 1F) }
  where
  open stdlib-CommutativeSemigroup S
      using ( setoid ; ∙-cong )
      renaming ( _∙_ to _·_ ; assoc to S-assoc ; comm to S-comm )

  𝑨 : Algebra _ _
  𝑨 = record { Domain = setoid ; Interp = interp }
    where
    interp : Func (⟨ Sig-Magma ⟩ setoid) setoid
    interp ⟨$⟩ (∙-Op , args)                            = args 0F · args 1F
    cong interp {∙-Op , _} {.∙-Op , _} (≡.refl , args≈) = ∙-cong (args≈ 0F) (args≈ 1F)

module _ {𝑪 : CommutativeSemigroup α ρ} where
  open CommutativeSemigroup-Op 𝑪
  open Setoid 𝔻[ proj₁ 𝑪 ]
  open CommutativeSemigroup-Op ⟪ ⟨ 𝑪 ⟩ᶜˢᵍ ⟫ᶜˢᵍ renaming ( _∙_ to _∙'_ )

  roundtrip-cbc-cs : (a b : 𝕌[ proj₁ 𝑪 ]) → (a ∙' b) ≈ (a ∙ b)
  roundtrip-cbc-cs a b = refl

module _ {S : stdlib-CommutativeSemigroup α ρ} where
  open stdlib-CommutativeSemigroup S using ( _≈_ ; _∙_ ; refl ) renaming ( Carrier to A )
  open stdlib-CommutativeSemigroup ⟨ ⟪ S ⟫ᶜˢᵍ ⟩ᶜˢᵍ using () renaming ( _∙_ to _∙'_ )

  roundtrip-bcb-cs : (a b : A) → (a ∙ b) ≈ (a ∙' b)
  roundtrip-bcb-cs a b = refl
```
