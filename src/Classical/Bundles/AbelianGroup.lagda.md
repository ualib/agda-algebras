---
layout: default
file: "src/Classical/Bundles/AbelianGroup.lagda.md"
title: "Classical.Bundles.AbelianGroup module"
date: "2026-05-30"
author: "the agda-algebras development team"
---

### Bundle bridge for abelian groups

This is the [Classical.Bundles.AbelianGroup][] module of the [Agda Universal Algebra Library][].

Mirror of the Group bridge with the added `comm` field; over `Sig-Group`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Bundles.AbelianGroup where

-- Imports from the Agda Standard Library -----------------------------------------
open import Algebra.Bundles  using ()              renaming (  AbelianGroup
                                                               to stdlib-AbelianGroup )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Product                           using ( _,_ ; proj₁ )
open import Function                               using ( Func )
open import Level                                  using ( Level )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  using (refl)
open Func renaming ( to to _⟨$⟩_ )

-- Imports from the Agda Universal Algebra Library --------------------------------
open import Classical.Signatures.Group             using  ( Sig-Group ; ∙-Op
                                                          ; ε-Op ; ⁻¹-Op )
open import Classical.Structures.AbelianGroup      using  ( AbelianGroup
                                                          ; module AbelianGroup-Op )
open import Classical.Theories.AbelianGroup        using  ( assoc ; idˡ ; idʳ
                                                          ; invˡ ; invʳ ; comm )
open import Setoid.Algebras.Basic {𝑆 = Sig-Group}  using  ( Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Signatures                      using  ( ⟨_⟩ )

private variable α ρ : Level

⟨_⟩ᵃᵍ : AbelianGroup α ρ → stdlib-AbelianGroup α ρ
⟨ 𝑨𝑩 ⟩ᵃᵍ = record
  { Carrier = 𝕌[ proj₁ 𝑨𝑩 ]
  ; _≈_     = _≈_
  ; _∙_     = _∙_
  ; ε       = ε
  ; _⁻¹     = _⁻¹
  ; isAbelianGroup = record
      { isGroup = record
          { isMonoid = record
              { isSemigroup = record
                  { isMagma = record { isEquivalence = isEquivalence ; ∙-cong = ∙-cong }
                  ; assoc   = assoc-law
                  }
              ; identity = idˡ-law , idʳ-law
              }
          ; inverse = invˡ-law , invʳ-law
          ; ⁻¹-cong = ⁻¹-cong
          }
      ; comm = comm-law
      }
  }
  where
  open AbelianGroup-Op 𝑨𝑩
  open Setoid 𝔻[ proj₁ 𝑨𝑩 ]

⟪_⟫ᵃᵍ : stdlib-AbelianGroup α ρ → AbelianGroup α ρ
⟪ G ⟫ᵃᵍ = 𝑨 , λ { assoc ρ → G-assoc (ρ 0F) (ρ 1F) (ρ 2F)
                ; idˡ   ρ → G-idˡ   (ρ 0F)
                ; idʳ   ρ → G-idʳ   (ρ 0F)
                ; invˡ  ρ → G-invˡ  (ρ 0F)
                ; invʳ  ρ → G-invʳ  (ρ 0F)
                ; comm  ρ → G-comm  (ρ 0F) (ρ 1F) }
  where
  open stdlib-AbelianGroup G
      using ( setoid ; ∙-cong ; ⁻¹-cong )
      renaming ( _∙_ to _·_ ; ε to e ; _⁻¹ to _⁻¹' ; assoc to G-assoc
               ; identityˡ to G-idˡ ; identityʳ to G-idʳ
               ; inverseˡ to G-invˡ ; inverseʳ to G-invʳ ; comm to G-comm )

  𝑨 : Algebra _ _
  𝑨 = record { Domain = setoid ; Interp = interp }
    where
    interp : Func (⟨ Sig-Group ⟩ setoid) setoid
    interp ⟨$⟩ (∙-Op  , args)                             = args 0F · args 1F
    interp ⟨$⟩ (ε-Op  , _)                                = e
    interp ⟨$⟩ (⁻¹-Op , args)                             = (args 0F) ⁻¹'
    cong interp {∙-Op  , _} {.∙-Op  , _} (refl , args≈) = ∙-cong (args≈ 0F) (args≈ 1F)
    cong interp {ε-Op  , _} {.ε-Op  , _} (refl , _)     = Setoid.refl setoid
    cong interp {⁻¹-Op , _} {.⁻¹-Op , _} (refl , args≈) = ⁻¹-cong (args≈ 0F)

module _ {𝑨𝑩 : AbelianGroup α ρ} where
  open AbelianGroup-Op 𝑨𝑩
  open Setoid 𝔻[ proj₁ 𝑨𝑩 ] using (_≈_) renaming (refl to refl≈ )
  open AbelianGroup-Op ⟪ ⟨ 𝑨𝑩 ⟩ᵃᵍ ⟫ᵃᵍ renaming ( _∙_ to _∙'_ ; ε to ε' ; _⁻¹ to _⁻¹' )

  roundtrip-cbc-∙-ag : (a b : 𝕌[ proj₁ 𝑨𝑩 ]) → (a ∙' b) ≈ (a ∙ b)
  roundtrip-cbc-∙-ag a b = refl≈

  roundtrip-cbc-ε-ag : ε' ≈ ε
  roundtrip-cbc-ε-ag = refl≈

  roundtrip-cbc-⁻¹-ag : (a : 𝕌[ proj₁ 𝑨𝑩 ]) → (a ⁻¹') ≈ (a ⁻¹)
  roundtrip-cbc-⁻¹-ag a = refl≈

module _ {G : stdlib-AbelianGroup α ρ} where
  open stdlib-AbelianGroup G              using ( _≈_ ; _∙_ ; ε ; _⁻¹ )
                                          renaming ( Carrier to A ; refl to refl≈ )

  open stdlib-AbelianGroup ⟨ ⟪ G ⟫ᵃᵍ ⟩ᵃᵍ  using ()
                                          renaming ( _∙_ to _∙'_ ; ε to ε' ; _⁻¹ to _⁻¹' )

  roundtrip-bcb-∙-ag : (a b : A) → (a ∙ b) ≈ (a ∙' b)
  roundtrip-bcb-∙-ag a b = refl≈

  roundtrip-bcb-ε-ag : ε ≈ ε'
  roundtrip-bcb-ε-ag = refl≈

  roundtrip-bcb-⁻¹-ag : (a : A) → (a ⁻¹) ≈ (a ⁻¹')
  roundtrip-bcb-⁻¹-ag a = refl≈
```
