---
layout: default
file: "src/Classical/Bundles/Semilattice.lagda.md"
title: "Classical.Bundles.Semilattice module"
date: "2026-05-27"
author: "the agda-algebras development team"
---

### Bundle bridge for semilattices

This is the [Classical.Bundles.Semilattice][] module of the [Agda Universal Algebra Library][].

Bridges `Classical.Structures.Semilattice` to stdlib's `Algebra.Lattice.Bundles.Semilattice`.
`Algebra.Lattice.Bundles.Semilattice` is the *unsigned* semilattice (operation
`_∙_`, neither meet nor join); the bridge is over `Sig-Magma` with the same
operation.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Bundles.Semilattice where

-- Imports from the Agda Standard Library -----------------------------------------
open import Algebra.Lattice.Bundles  using () renaming ( Semilattice to stdlib-Semilattice )
open import Data.Fin.Patterns        using ( 0F ; 1F ; 2F )
open import Data.Product             using ( _,_ ; proj₁ )
open import Function                 using ( Func )
open import Level                    using ( Level )
open import Relation.Binary          using ( Setoid )
import Relation.Binary.PropositionalEquality as ≡
open Func renaming ( to to _⟨$⟩_ )

-- Imports from the Agda Universal Algebra Library --------------------------------
open import Classical.Signatures.Magma             using  ( ∙-Op ; Sig-Magma )
open import Classical.Structures.Semilattice       using  ( Semilattice ; module Semilattice-Op )
open import Classical.Theories.Semilattice         using  ( assoc ; comm ; idem )
open import Setoid.Algebras.Basic {𝑆 = Sig-Magma}  using ( Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Signatures                      using  ( ⟨_⟩ )

private variable α ρ : Level

⟨_⟩ˢˡ : Semilattice α ρ → stdlib-Semilattice α ρ
⟨ 𝑺 ⟩ˢˡ = record
  { Carrier = 𝕌[ proj₁ 𝑺 ]
  ; _≈_     = _≈_
  ; _∙_     = _∙_
  ; isSemilattice = record
      { isBand = record
          { isSemigroup = record
              { isMagma = record { isEquivalence = isEquivalence ; ∙-cong = ∙-cong }
              ; assoc   = assoc-law
              }
          ; idem    = idem-law
          }
      ; comm    = comm-law
      }
  }
  where
  open Semilattice-Op 𝑺
  open Setoid 𝔻[ proj₁ 𝑺 ]

⟪_⟫ˢˡ : stdlib-Semilattice α ρ → Semilattice α ρ
⟪ S ⟫ˢˡ = 𝑨 , λ  { assoc ρ → S-assoc (ρ 0F) (ρ 1F) (ρ 2F)
                 ; comm  ρ → S-comm  (ρ 0F) (ρ 1F)
                 ; idem  ρ → S-idem  (ρ 0F) }
  where
  open stdlib-Semilattice S using ( setoid ; ∙-cong ) renaming  ( _∙_    to _·_
                                                                ; assoc  to S-assoc
                                                                ; comm   to S-comm
                                                                ; idem   to S-idem )

  𝑨 : Algebra _ _
  𝑨 = record { Domain = setoid ; Interp = interp }
    where
    interp : Func (⟨ Sig-Magma ⟩ setoid) setoid
    interp ⟨$⟩ (∙-Op , args) = args 0F · args 1F
    cong interp {∙-Op , _} {.∙-Op , _} (≡.refl , args≈) = ∙-cong (args≈ 0F) (args≈ 1F)

module _ {𝑺 : Semilattice α ρ} where
  open Semilattice-Op 𝑺
  open Setoid 𝔻[ proj₁ 𝑺 ]
  open Semilattice-Op ⟪ ⟨ 𝑺 ⟩ˢˡ ⟫ˢˡ renaming ( _∙_ to _∙'_ )

  roundtrip-cbc-sl : (a b : 𝕌[ proj₁ 𝑺 ]) → a ∙' b ≈ a ∙ b
  roundtrip-cbc-sl a b = refl

module _ {S : stdlib-Semilattice α ρ} where
  open stdlib-Semilattice S using ( _≈_ ; _∙_ ; refl ) renaming ( Carrier to A )
  open stdlib-Semilattice ⟨ ⟪ S ⟫ˢˡ ⟩ˢˡ using () renaming ( _∙_ to _∙'_ )

  roundtrip-bcb-sl : (a b : A) → a ∙ b ≈ a ∙' b
  roundtrip-bcb-sl a b = refl
```
