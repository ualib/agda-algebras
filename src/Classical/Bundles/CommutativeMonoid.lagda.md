---
layout: default
file: "src/Classical/Bundles/CommutativeMonoid.lagda.md"
title: "Classical.Bundles.CommutativeMonoid module"
date: "2026-05-24"
author: "the agda-algebras development team"
---

### <a id="classical-bundles-commutativemonoid">Bundle bridge for commutative monoids</a>

This is the [Classical.Bundles.CommutativeMonoid][] module of the [Agda Universal Algebra Library][].

Mirror of the Monoid bridge with the added `comm` field; over `Sig-Monoid`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Bundles.CommutativeMonoid where

-- Imports from the Agda Standard Library -----------------------------------------
open import Algebra.Bundles     using () renaming (  CommutativeMonoid
                                                     to stdlib-CommutativeMonoid )
open import Data.Fin.Patterns   using ( 0F ; 1F ; 2F )
open import Data.Product        using ( _,_ ; proj₁ )
open import Function            using ( Func )
open import Level               using ( Level )
open import Relation.Binary     using ( Setoid )
import Relation.Binary.PropositionalEquality as ≡
open Func renaming ( to to _⟨$⟩_ )

-- Imports from the Agda Universal Algebra Library --------------------------------
open import Classical.Signatures.Monoid                using  ( Sig-Monoid ; ∙-Op ; ε-Op )
open import Classical.Structures.CommutativeMonoid     using  ( CommutativeMonoid
                                                              ; module CommutativeMonoid-Op )
open import Classical.Theories.CommutativeMonoid       using  ( assoc ; idˡ ; idʳ ; comm )
open import Setoid.Algebras.Basic {𝑆 = Sig-Monoid}     using  ( Algebra ; ⟨_⟩ ; 𝕌[_] ; 𝔻[_] )

private variable α ρ : Level

⟨_⟩ᶜᵐ : CommutativeMonoid α ρ → stdlib-CommutativeMonoid α ρ
⟨ 𝑪 ⟩ᶜᵐ = record
  { Carrier = 𝕌[ proj₁ 𝑪 ]
  ; _≈_     = _≈_
  ; _∙_     = _∙_
  ; ε       = ε
  ; isCommutativeMonoid = record
      { isMonoid = record
          { isSemigroup = record
              { isMagma = record { isEquivalence = isEquivalence ; ∙-cong = ∙-cong }
              ; assoc   = assoc-law
              }
          ; identity = idˡ-law , idʳ-law
          }
      ; comm = comm-law
      }
  }
  where
  open CommutativeMonoid-Op 𝑪
  open Setoid 𝔻[ proj₁ 𝑪 ]

⟪_⟫ᶜᵐ : stdlib-CommutativeMonoid α ρ → CommutativeMonoid α ρ
⟪ M ⟫ᶜᵐ = 𝑨 , λ { assoc ρ → M-assoc (ρ 0F) (ρ 1F) (ρ 2F)
                ; idˡ   ρ → M-idˡ   (ρ 0F)
                ; idʳ   ρ → M-idʳ   (ρ 0F)
                ; comm  ρ → M-comm  (ρ 0F) (ρ 1F) }
  where
  open stdlib-CommutativeMonoid M
      using ( setoid ; ∙-cong )
      renaming ( _∙_ to _·_ ; ε to e ; assoc to M-assoc
               ; identityˡ to M-idˡ ; identityʳ to M-idʳ ; comm to M-comm )

  𝑨 : Algebra _ _
  𝑨 = record { Domain = setoid ; Interp = interp }
    where
    interp : Func (⟨ Sig-Monoid ⟩ setoid) setoid
    interp ⟨$⟩ (∙-Op , args)                            = args 0F · args 1F
    interp ⟨$⟩ (ε-Op , _)                               = e
    cong interp {∙-Op , _} {.∙-Op , _} (≡.refl , args≈) = ∙-cong (args≈ 0F) (args≈ 1F)
    cong interp {ε-Op , _} {.ε-Op , _} (≡.refl , _)     = Setoid.refl setoid

module _ {𝑪 : CommutativeMonoid α ρ} where
  open CommutativeMonoid-Op 𝑪
  open Setoid 𝔻[ proj₁ 𝑪 ]
  open CommutativeMonoid-Op ⟪ ⟨ 𝑪 ⟩ᶜᵐ ⟫ᶜᵐ renaming ( _∙_ to _∙'_ ; ε to ε' )

  roundtrip-cbc-∙-cm : (a b : 𝕌[ proj₁ 𝑪 ]) → (a ∙' b) ≈ (a ∙ b)
  roundtrip-cbc-∙-cm a b = refl

  roundtrip-cbc-ε-cm : ε' ≈ ε
  roundtrip-cbc-ε-cm = refl

module _ {M : stdlib-CommutativeMonoid α ρ} where
  open stdlib-CommutativeMonoid M using ( _≈_ ; _∙_ ; ε ; refl ) renaming ( Carrier to A )
  open stdlib-CommutativeMonoid ⟨ ⟪ M ⟫ᶜᵐ ⟩ᶜᵐ using () renaming ( _∙_ to _∙'_ ; ε to ε' )

  roundtrip-bcb-∙-cm : (a b : A) → (a ∙ b) ≈ (a ∙' b)
  roundtrip-bcb-∙-cm a b = refl

  roundtrip-bcb-ε-cm : ε ≈ ε'
  roundtrip-bcb-ε-cm = refl
```

--------------------------------------

{% include UALib.Links.md %}
