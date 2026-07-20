---
layout: default
file: "src/Classical/Bundles/Ring.lagda.md"
title: "Classical.Bundles.Ring module"
date: "2026-05-30"
author: "the agda-algebras development team"
---

### Bundle bridge for rings

This is the [Classical.Bundles.Ring][] module of the [Agda Universal Algebra Library][].

The bidirectional bridge between the Σ-typed core of [`Classical.Structures.Ring`][Classical.Structures.Ring]
and the record-typed `Algebra.Bundles.Ring` in the standard library.  The round-trip
is stated *pointwise* per [ADR-002 v2 §6](../../docs/adr/002-classical-layer-design.md);
the eleven curried laws arrive ready-made from `Ring-Op`, so the core-to-bundle
direction is a (deeply nested) record-shuffle and the reverse direction is one
`Func` plus the eleven equation clauses.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Bundles.Ring where

-- Imports from the Agda Standard Library -----------------------------------------
open import Algebra.Bundles     using () renaming ( Ring to stdlib-Ring )
open import Data.Fin.Patterns   using ( 0F ; 1F ; 2F )
open import Data.Product        using ( _,_ ; proj₁ )
open import Function            using ( Func )
open import Level               using ( Level )
open import Relation.Binary     using ( Setoid )
import Relation.Binary.PropositionalEquality as ≡
open Func renaming ( to to _⟨$⟩_ )

-- Imports from the Agda Universal Algebra Library --------------------------------
open import Classical.Signatures.Ring             using  ( Sig-Ring ; +-Op ; 0-Op
                                                         ; -Op ; ·-Op ; 1-Op )
open import Classical.Structures.Ring             using  ( Ring ; module Ring-Op )
open import Classical.Theories.Ring               using  ( +-assoc ; +-idˡ ; +-idʳ ; +-invˡ
                                                         ; +-invʳ ; +-comm ; ·-assoc ; ·-idˡ
                                                         ; ·-idʳ ; distribˡ ; distribʳ )
open import Setoid.Algebras.Basic  using  ( Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Signatures                     using  ( ⟨_⟩ )

private variable α ρ : Level
```
-->

#### Core to stdlib bundle

```agda
⟨_⟩ʳᵍ : Ring α ρ → stdlib-Ring α ρ
⟨ 𝑹 ⟩ʳᵍ = record
  { Carrier = 𝕌[ 𝑨 ]
  ; _≈_     = _≈_
  ; _+_     = _+_
  ; _*_     = _·_
  ; -_      = -_
  ; 0#      = 0R
  ; 1#      = 1R
  ; isRing  = record
      { +-isAbelianGroup = record
          { isGroup = record
              { isMonoid = record
                  { isSemigroup = record
                      { isMagma = record { isEquivalence = isEquivalence ; ∙-cong = +-cong }
                      ; assoc   = +-assoc-law
                      }
                  ; identity = +-idˡ-law , +-idʳ-law
                  }
              ; inverse = +-invˡ-law , +-invʳ-law
              ; ⁻¹-cong = neg-cong
              }
          ; comm = +-comm-law
          }
      ; *-cong     = ·-cong
      ; *-assoc    = ·-assoc-law
      ; *-identity = ·-idˡ-law , ·-idʳ-law
      ; distrib    = distribˡ-law , distribʳ-law
      }
  }
  where
  𝑨 = proj₁ 𝑹
  open Ring-Op 𝑹
  open Setoid 𝔻[ 𝑨 ]
```

#### Stdlib bundle to core

```agda
⟪_⟫ʳᵍ : stdlib-Ring α ρ → Ring α ρ
⟪ R ⟫ʳᵍ = 𝑨 , λ  { +-assoc   ρ → R-+assoc    (ρ 0F) (ρ 1F) (ρ 2F)
                 ; +-idˡ     ρ → R-+idˡ      (ρ 0F)
                 ; +-idʳ     ρ → R-+idʳ      (ρ 0F)
                 ; +-invˡ    ρ → R-+invˡ     (ρ 0F)
                 ; +-invʳ    ρ → R-+invʳ     (ρ 0F)
                 ; +-comm    ρ → R-+comm     (ρ 0F) (ρ 1F)
                 ; ·-assoc   ρ → R-*assoc    (ρ 0F) (ρ 1F) (ρ 2F)
                 ; ·-idˡ     ρ → R-*idˡ      (ρ 0F)
                 ; ·-idʳ     ρ → R-*idʳ      (ρ 0F)
                 ; distribˡ  ρ → R-distribˡ  (ρ 0F) (ρ 1F) (ρ 2F)
                 ; distribʳ  ρ → R-distribʳ  (ρ 0F) (ρ 1F) (ρ 2F) }
  where
  open stdlib-Ring R using ( setoid ; +-cong ; -‿cong ; *-cong )
    renaming  ( _+_         to _⊕_         ; _*_         to _⊛_ ; -_  to ⊖_
              ; 0#          to z           ; 1#          to e
              ; +-assoc     to R-+assoc    ; +-comm      to R-+comm
              ; +-identityˡ to R-+idˡ      ; +-identityʳ to R-+idʳ
              ; -‿inverseˡ  to R-+invˡ     ; -‿inverseʳ  to R-+invʳ
              ; *-assoc     to R-*assoc
              ; *-identityˡ to R-*idˡ      ; *-identityʳ to R-*idʳ
              ; distribˡ    to R-distribˡ  ; distribʳ    to R-distribʳ )

  𝑨 : Algebra {𝑆 = Sig-Ring} _ _
  𝑨 = record { Domain = setoid ; Interp = interp }
    where
    interp : Func (⟨ Sig-Ring ⟩ setoid) setoid
    interp ⟨$⟩ (+-Op , args)                             = args 0F ⊕ args 1F
    interp ⟨$⟩ (0-Op , _)                                = z
    interp ⟨$⟩ (-Op  , args)                             = ⊖ (args 0F)
    interp ⟨$⟩ (·-Op , args)                             = args 0F ⊛ args 1F
    interp ⟨$⟩ (1-Op , _)                                = e
    cong interp {+-Op , _} {.+-Op , _} (≡.refl , args≈)  = +-cong (args≈ 0F) (args≈ 1F)
    cong interp {0-Op , _} {.0-Op , _} (≡.refl , _)      = Setoid.refl setoid
    cong interp { -Op , _} {.-Op  , _} (≡.refl , args≈)  = -‿cong (args≈ 0F)
    cong interp {·-Op , _} {.·-Op , _} (≡.refl , args≈)  = *-cong (args≈ 0F) (args≈ 1F)
    cong interp {1-Op , _} {.1-Op , _} (≡.refl , _)      = Setoid.refl setoid
```

#### Pointwise round-trip

```agda
module _ {𝑹 : Ring α ρ} where
  open Ring-Op 𝑹
  open Setoid 𝔻[ proj₁ 𝑹 ]
  open Ring-Op ⟪ ⟨ 𝑹 ⟩ʳᵍ ⟫ʳᵍ renaming  ( _+_  to _+'_
                                       ; _·_  to _·'_
                                       ; -_   to -'_
                                       ; 0R   to 0R'
                                       ; 1R   to 1R' )

  roundtrip-cbc-+-ring : (a b : 𝕌[ proj₁ 𝑹 ]) → a +' b ≈ a + b
  roundtrip-cbc-+-ring a b = refl

  roundtrip-cbc-·-ring : (a b : 𝕌[ proj₁ 𝑹 ]) → a ·' b ≈ a · b
  roundtrip-cbc-·-ring a b = refl

  roundtrip-cbc-neg-ring : (a : 𝕌[ proj₁ 𝑹 ]) → -' a ≈ - a
  roundtrip-cbc-neg-ring a = refl

  roundtrip-cbc-0-ring : 0R' ≈ 0R
  roundtrip-cbc-0-ring = refl

  roundtrip-cbc-1-ring : 1R' ≈ 1R
  roundtrip-cbc-1-ring = refl

module _ {R : stdlib-Ring α ρ} where
  open stdlib-Ring R using ( _≈_ ; _+_ ; _*_ ; -_ ; 0# ; 1# ; refl ) renaming ( Carrier to A )
  open stdlib-Ring ⟨ ⟪ R ⟫ʳᵍ ⟩ʳᵍ using () renaming  ( _+_ to _+'_
                                                    ; _*_ to _*'_
                                                    ; -_  to -'_
                                                    ; 0#  to 0#'
                                                    ; 1#  to 1#' )

  roundtrip-bcb-+-ring : (a b : A) → a + b ≈ a +' b
  roundtrip-bcb-+-ring a b = refl

  roundtrip-bcb-·-ring : (a b : A) → a * b ≈ a *' b
  roundtrip-bcb-·-ring a b = refl

  roundtrip-bcb-neg-ring : (a : A) → - a ≈ -' a
  roundtrip-bcb-neg-ring a = refl

  roundtrip-bcb-0-ring : 0# ≈ 0#'
  roundtrip-bcb-0-ring = refl

  roundtrip-bcb-1-ring : 1# ≈ 1#'
  roundtrip-bcb-1-ring = refl
```
