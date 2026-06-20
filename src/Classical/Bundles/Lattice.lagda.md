---
layout: default
file: "src/Classical/Bundles/Lattice.lagda.md"
title: "Classical.Bundles.Lattice module"
date: "2026-05-28"
author: "the agda-algebras development team"
---

### Bundle bridge for lattices

This is the [Classical.Bundles.Lattice][] module of the [Agda Universal Algebra Library][].

Bridges `Classical.Structures.Lattice` to stdlib's `Algebra.Lattice.Bundles.Lattice`.
This is the first bundle bridge with two distinct binary operations; like the
Semilattice bridge, its stdlib target lives in `Algebra.Lattice.Bundles` rather
than `Algebra.Bundles`.

Two derivations cross the bridge.  The forward direction (`⟨_⟩ˡᵃ`) needs the
stdlib-canonical absorption form `∨ Absorbs ∧` — i.e. `x ∨ (x ∧ y) ≈ x` — from
our `absorbʳ-law` (which has the form `(x ∧ y) ∨ x ≈ x`); this is one ∨-comm
step.  The reverse direction (`⟪_⟫ˡᵃ`) needs `∧-idem`, `∨-idem`, and the form
`(x ∧ y) ∨ x ≈ x` from a stdlib lattice's `absorptive` (which provides
`x ∨ (x ∧ y) ≈ x` and `x ∧ (x ∨ y) ≈ x`); the idempotencies are the standard
two-step derivation from absorption, the absorbʳ form is one ∨-comm step.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Bundles.Lattice where

-- Imports from the Agda Standard Library -----------------------------------------
open import Algebra.Lattice.Bundles  using () renaming ( Lattice to stdlib-Lattice )
open import Data.Fin.Patterns        using ( 0F ; 1F ; 2F )
open import Data.Product             using ( _,_ ; proj₁ ; proj₂ )
open import Function                 using ( Func )
open import Level                    using ( Level )
open import Relation.Binary          using ( Setoid )
import Relation.Binary.PropositionalEquality as ≡
open Func renaming ( to to _⟨$⟩_ )

-- Imports from the Agda Universal Algebra Library --------------------------------
open import Classical.Signatures.Lattice             using  ( ∧-Op ; ∨-Op ; Sig-Lattice )
open import Classical.Structures.Lattice             using  ( Lattice ; module Lattice-Op )
open import Classical.Theories.Lattice               using  ( ∧-assoc ; ∧-comm ; ∧-idem
                                                            ; ∨-assoc ; ∨-comm ; ∨-idem
                                                            ; absorbˡ ; absorbʳ )
open import Setoid.Algebras.Basic {𝑆 = Sig-Lattice}  using  ( Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Signatures                        using  ( ⟨_⟩ )

private variable α ρ : Level

⟨_⟩ˡᵃ : Lattice α ρ → stdlib-Lattice α ρ
⟨ 𝑳 ⟩ˡᵃ = record
  { Carrier = 𝕌[ proj₁ 𝑳 ]
  ; _≈_     = _≈_
  ; _∨_     = _∨_
  ; _∧_     = _∧_
  ; isLattice = record
      { isEquivalence = isEquivalence
      ; ∨-comm        = ∨-comm-law
      ; ∨-assoc       = ∨-assoc-law
      ; ∨-cong        = ∨-cong
      ; ∧-comm        = ∧-comm-law
      ; ∧-assoc       = ∧-assoc-law
      ; ∧-cong        = ∧-cong
      ; absorptive    = ∨-absorbs-∧ , absorbˡ-law
      }
  }
  where
  open Lattice-Op 𝑳
  open Setoid 𝔻[ proj₁ 𝑳 ]

  -- stdlib's first absorption is x ∨ (x ∧ y) ≈ x; our absorbʳ-law is (x ∧ y) ∨ x ≈ x.
  ∨-absorbs-∧ : ∀ x y → (x ∨ (x ∧ y)) ≈ x
  ∨-absorbs-∧ x y = trans (∨-comm-law x (x ∧ y)) (absorbʳ-law x y)

⟪_⟫ˡᵃ : stdlib-Lattice α ρ → Lattice α ρ
⟪ L ⟫ˡᵃ = 𝑨 , λ { ∧-assoc ρ → L-∧-assoc (ρ 0F) (ρ 1F) (ρ 2F)
                ; ∧-comm  ρ → L-∧-comm  (ρ 0F) (ρ 1F)
                ; ∧-idem  ρ → ∧-idem-derived (ρ 0F)
                ; ∨-assoc ρ → L-∨-assoc (ρ 0F) (ρ 1F) (ρ 2F)
                ; ∨-comm  ρ → L-∨-comm  (ρ 0F) (ρ 1F)
                ; ∨-idem  ρ → ∨-idem-derived (ρ 0F)
                ; absorbˡ ρ → L-∧-absorbs-∨ (ρ 0F) (ρ 1F)
                ; absorbʳ ρ → absorbʳ-derived (ρ 0F) (ρ 1F)
                }
  where
  open stdlib-Lattice L
      using ( setoid ; ∧-cong ; ∨-cong )
      renaming ( _∨_ to _∨'_ ; _∧_ to _∧'_
               ; ∨-assoc to L-∨-assoc ; ∨-comm to L-∨-comm
               ; ∧-assoc to L-∧-assoc ; ∧-comm to L-∧-comm
               ; ∨-absorbs-∧ to L-∨-absorbs-∧ ; ∧-absorbs-∨ to L-∧-absorbs-∨ )
  open Setoid setoid

  -- Idempotency derived from absorption: x ∧ x ≈ x ∧ (x ∨ (x ∧ x)) [by L-∨-absorbs-∧]
  --                                            ≈ x                 [by L-∧-absorbs-∨]
  ∧-idem-derived : ∀ x → (x ∧' x) ≈ x
  ∧-idem-derived x = trans (∧-cong refl (sym (L-∨-absorbs-∧ x x))) (L-∧-absorbs-∨ x (x ∧' x))

  ∨-idem-derived : ∀ x → (x ∨' x) ≈ x
  ∨-idem-derived x = trans (∨-cong refl (sym (L-∧-absorbs-∨ x x))) (L-∨-absorbs-∧ x (x ∨' x))

  -- (x ∧ y) ∨ x ≈ x ∨ (x ∧ y) ≈ x
  absorbʳ-derived : ∀ x y → ((x ∧' y) ∨' x) ≈ x
  absorbʳ-derived x y = trans (L-∨-comm (x ∧' y) x) (L-∨-absorbs-∧ x y)

  𝑨 : Algebra _ _
  𝑨 = record { Domain = setoid ; Interp = interp }
    where
    interp : Func (⟨ Sig-Lattice ⟩ setoid) setoid
    interp ⟨$⟩ (∧-Op , args)                            = args 0F ∧' args 1F
    interp ⟨$⟩ (∨-Op , args)                            = args 0F ∨' args 1F
    cong interp {∧-Op , _} {.∧-Op , _} (≡.refl , args≈) = ∧-cong (args≈ 0F) (args≈ 1F)
    cong interp {∨-Op , _} {.∨-Op , _} (≡.refl , args≈) = ∨-cong (args≈ 0F) (args≈ 1F)

module _ {𝑳 : Lattice α ρ} where
  open Lattice-Op 𝑳
  open Setoid 𝔻[ proj₁ 𝑳 ]
  open Lattice-Op ⟪ ⟨ 𝑳 ⟩ˡᵃ ⟫ˡᵃ renaming ( _∧_ to _∧'_ ; _∨_ to _∨'_ )

  roundtrip-cbc-∧-la : (a b : 𝕌[ proj₁ 𝑳 ]) → (a ∧' b) ≈ (a ∧ b)
  roundtrip-cbc-∧-la a b = refl

  roundtrip-cbc-∨-la : (a b : 𝕌[ proj₁ 𝑳 ]) → (a ∨' b) ≈ (a ∨ b)
  roundtrip-cbc-∨-la a b = refl

module _ {L : stdlib-Lattice α ρ} where
  open stdlib-Lattice L using ( _≈_ ; _∧_ ; _∨_ ; refl ) renaming ( Carrier to A )
  open stdlib-Lattice ⟨ ⟪ L ⟫ˡᵃ ⟩ˡᵃ using () renaming ( _∧_ to _∧'_ ; _∨_ to _∨'_ )

  roundtrip-bcb-∧-la : (a b : A) → (a ∧ b) ≈ (a ∧' b)
  roundtrip-bcb-∧-la a b = refl

  roundtrip-bcb-∨-la : (a b : A) → (a ∨ b) ≈ (a ∨' b)
  roundtrip-bcb-∨-la a b = refl
```

--------------------------------------

{% include UALib.Links.md %}
