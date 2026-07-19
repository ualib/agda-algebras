---
layout: default
file: "src/Classical/Bundles/Monoid.lagda.md"
title: "Classical.Bundles.Monoid module"
date: "2026-05-24"
author: "the agda-algebras development team"
---

### Bundle bridge for monoids

This is the [Classical.Bundles.Monoid][] module of the [Agda Universal Algebra Library][].

The bidirectional bridge between the Σ-typed core of [`Classical.Structures.Monoid`][Classical.Structures.Monoid]
and the record-typed `Algebra.Bundles.Monoid` in the standard library.  As with the
Semigroup bridge, the round-trip is stated *pointwise* per
[ADR-002 v2 §6](../../docs/adr/002-classical-layer-design.md); the curried laws
`assoc-law`, `idˡ-law`, `idʳ-law` arrive ready-made from `Monoid-Op`, so each
direction is a thin record-shuffle.  The only addition over the Semigroup bridge is
the nullary `ε` field and the `ε-Op` clause of the reverse interpretation.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Bundles.Monoid where

-- Imports from the Agda Standard Library -----------------------------------------
open import Algebra.Bundles     using () renaming ( Monoid to stdlib-Monoid )
open import Data.Fin.Patterns   using ( 0F ; 1F ; 2F )
open import Data.Product        using ( _,_ ; proj₁ )
open import Function            using ( Func )
open import Level               using ( Level )
open import Relation.Binary     using ( Setoid )
import Relation.Binary.PropositionalEquality as ≡
open Func renaming ( to to _⟨$⟩_ )

-- Imports from the Agda Universal Algebra Library --------------------------------
open import Classical.Signatures.Monoid             using ( Sig-Monoid ; ∙-Op ; ε-Op )
open import Classical.Structures.Monoid             using ( Monoid ; module Monoid-Op )
open import Classical.Theories.Monoid               using ( assoc ; idˡ ; idʳ )
open import Setoid.Algebras.Basic  using ( Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Signatures                       using ( ⟨_⟩ )

private variable α ρ : Level
```
-->

#### Core to stdlib bundle

```agda
⟨_⟩ᵐᵒ : Monoid α ρ → stdlib-Monoid α ρ
⟨ 𝑴 ⟩ᵐᵒ = record
  { Carrier  = 𝕌[ 𝑨 ]
  ; _≈_      = _≈_
  ; _∙_      = _∙_
  ; ε        = ε
  ; isMonoid = record
      { isSemigroup = record
          { isMagma = record { isEquivalence = isEquivalence ; ∙-cong = ∙-cong }
          ; assoc   = assoc-law
          }
      ; identity = idˡ-law , idʳ-law
      }
  }
  where
  𝑨 = proj₁ 𝑴
  open Monoid-Op 𝑴
  open Setoid 𝔻[ 𝑨 ]
```

#### Stdlib bundle to core

```agda
⟪_⟫ᵐᵒ : stdlib-Monoid α ρ → Monoid α ρ
⟪ M ⟫ᵐᵒ = 𝑨 , λ  { assoc ρ → M-assoc (ρ 0F) (ρ 1F) (ρ 2F)
                 ; idˡ   ρ → M-idˡ   (ρ 0F)
                 ; idʳ   ρ → M-idʳ   (ρ 0F) }
  where
  open stdlib-Monoid M using ( setoid ; ∙-cong ) renaming  ( _∙_       to _·_
                                                           ; ε         to e
                                                           ; assoc     to M-assoc
                                                           ; identityˡ to M-idˡ
                                                           ; identityʳ to M-idʳ )

  𝑨 : Algebra {𝑆 = Sig-Monoid} _ _
  𝑨 = record { Domain = setoid ; Interp = interp }
    where
    interp : Func (⟨ Sig-Monoid ⟩ setoid) setoid
    interp ⟨$⟩ (∙-Op , args)                            = args 0F · args 1F
    interp ⟨$⟩ (ε-Op , _)                               = e
    cong interp {∙-Op , _} {.∙-Op , _} (≡.refl , args≈) = ∙-cong (args≈ 0F) (args≈ 1F)
    cong interp {ε-Op , _} {.ε-Op , _} (≡.refl , _)     = Setoid.refl setoid
```

#### Pointwise round-trip

```agda
module _ {𝑴 : Monoid α ρ} where
  open Monoid-Op 𝑴
  open Setoid 𝔻[ proj₁ 𝑴 ] using (_≈_) renaming (refl to ≈refl)
  open Monoid-Op ⟪ ⟨ 𝑴 ⟩ᵐᵒ ⟫ᵐᵒ renaming ( _∙_ to _∙'_ ; ε to ε' )

  roundtrip-cbc-∙-mn : (a b : 𝕌[ proj₁ 𝑴 ]) → (a ∙' b) ≈ (a ∙ b)
  roundtrip-cbc-∙-mn a b = ≈refl

  roundtrip-cbc-ε-mn : ε' ≈ ε
  roundtrip-cbc-ε-mn = ≈refl

module _ {M : stdlib-Monoid α ρ} where
  open stdlib-Monoid M using ( _≈_ ; _∙_ ; ε ; refl ) renaming ( Carrier to A )
  open stdlib-Monoid ⟨ ⟪ M ⟫ᵐᵒ ⟩ᵐᵒ using () renaming ( _∙_ to _∙'_ ; ε to ε' )

  roundtrip-bcb-∙-mn : (a b : A) → (a ∙ b) ≈ (a ∙' b)
  roundtrip-bcb-∙-mn a b = refl

  roundtrip-bcb-ε-mn : ε ≈ ε'
  roundtrip-bcb-ε-mn = refl
```
