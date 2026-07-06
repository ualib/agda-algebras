---
layout: default
file: "src/Classical/Bundles/DistributiveLattice.lagda.md"
title: "Classical.Bundles.DistributiveLattice module"
date: "2026-05-31"
author: "the agda-algebras development team"
---

### Bundle bridge for distributive lattices {#classical-bundles-distributivelattice}

This is the [Classical.Bundles.DistributiveLattice][] module of the [Agda Universal Algebra Library][].

Bridges [`Classical.Structures.DistributiveLattice`][] to the standard library's
`Algebra.Lattice.Bundles.DistributiveLattice`.  Like the
[Lattice bridge][Classical.Bundles.Lattice], its stdlib target lives in
`Algebra.Lattice.Bundles`.

The forward direction (`⟨_⟩ᵈˡ`) builds an `IsDistributiveLattice` from our laws:
its `isLattice` field is the same record the Lattice bridge produces (one `∨-comm`
step bridges our `absorbʳ-law` to stdlib's `∨-absorbs-∧`), and the two
`DistributesOver` fields each pair a left and a right curried law — both of which
`DistributiveLattice-Op` supplies.

The reverse direction (`⟪_⟫ᵈˡ`) reads stdlib's `∨-distribˡ-∧` and `∧-distribˡ-∨`
back as the two left distributivity equations and reuses the Lattice-bridge
derivations (idempotency from absorption, the `absorbʳ` form by one `∨-comm` step)
for the eight shared equations.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Bundles.DistributiveLattice where

-- Imports from the Agda Standard Library -------------------------------------
open import Algebra.Lattice.Bundles  using ()
                                     renaming (  DistributiveLattice
                                                 to stdlib-DistributiveLattice )
open import Data.Fin.Patterns        using ( 0F ; 1F ; 2F )
open import Data.Product             using ( _,_ ; proj₁ )
open import Function                 using ( Func )
open import Level                    using ( Level )
open import Relation.Binary          using ( Setoid )
open import Relation.Binary.PropositionalEquality using (refl)
open Func renaming ( to to _⟨$⟩_ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Signatures.Lattice              using  ( ∧-Op ; ∨-Op ; Sig-Lattice )
open import Classical.Structures.DistributiveLattice  using  ( DistributiveLattice
                                                             ; module DistributiveLattice-Op )
open import Classical.Theories.DistributiveLattice    using  ( ∧-assoc ; ∧-comm ; ∧-idem
                                                             ; ∨-assoc ; ∨-comm ; ∨-idem
                                                             ; absorbˡ ; absorbʳ
                                                             ; ∧-distribˡ ; ∨-distribˡ )
open import Setoid.Algebras.Basic {𝑆 = Sig-Lattice}   using  ( Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Signatures                         using  ( ⟨_⟩ )

private variable α ρ : Level
```
-->

```agda
⟨_⟩ᵈˡ : DistributiveLattice α ρ → stdlib-DistributiveLattice α ρ
⟨ 𝑫 ⟩ᵈˡ = record
  { Carrier = 𝕌[ proj₁ 𝑫 ]
  ; _≈_     = _≈_
  ; _∨_     = _∨_
  ; _∧_     = _∧_
  ; isDistributiveLattice = record
      { isLattice = record
          { isEquivalence = isEquivalence
          ; ∨-comm        = ∨-comm-law
          ; ∨-assoc       = ∨-assoc-law
          ; ∨-cong        = ∨-cong
          ; ∧-comm        = ∧-comm-law
          ; ∧-assoc       = ∧-assoc-law
          ; ∧-cong        = ∧-cong
          ; absorptive    = ∨-absorbs-∧ , absorbˡ-law
          }
      ; ∨-distrib-∧ = ∨-distribˡ-law , ∨-distribʳ-law
      ; ∧-distrib-∨ = ∧-distribˡ-law , ∧-distribʳ-law
      }
  }
  where
  open DistributiveLattice-Op 𝑫
  open Setoid 𝔻[ proj₁ 𝑫 ] using ( _≈_ ; isEquivalence) renaming (refl to ≈refl ; trans to ≈trans )

  -- stdlib's first absorption is x ∨ (x ∧ y) ≈ x; our absorbʳ-law is (x ∧ y) ∨ x ≈ x.
  ∨-absorbs-∧ : ∀ x y → x ∨ (x ∧ y) ≈ x
  ∨-absorbs-∧ x y = ≈trans (∨-comm-law x (x ∧ y)) (absorbʳ-law x y)

⟪_⟫ᵈˡ : stdlib-DistributiveLattice α ρ → DistributiveLattice α ρ
⟪ L ⟫ᵈˡ = 𝑨 , λ { ∧-assoc    ρ → L-∧-assoc (ρ 0F) (ρ 1F) (ρ 2F)
                ; ∧-comm     ρ → L-∧-comm  (ρ 0F) (ρ 1F)
                ; ∧-idem     ρ → ∧-idem-derived (ρ 0F)
                ; ∨-assoc    ρ → L-∨-assoc (ρ 0F) (ρ 1F) (ρ 2F)
                ; ∨-comm     ρ → L-∨-comm  (ρ 0F) (ρ 1F)
                ; ∨-idem     ρ → ∨-idem-derived (ρ 0F)
                ; absorbˡ    ρ → L-∧-absorbs-∨ (ρ 0F) (ρ 1F)
                ; absorbʳ    ρ → absorbʳ-derived (ρ 0F) (ρ 1F)
                ; ∧-distribˡ ρ → L-∧-distribˡ-∨ (ρ 0F) (ρ 1F) (ρ 2F)
                ; ∨-distribˡ ρ → L-∨-distribˡ-∧ (ρ 0F) (ρ 1F) (ρ 2F)
                }
  where
  open stdlib-DistributiveLattice L
      using ( setoid ; ∧-cong ; ∨-cong )
      renaming ( _∨_ to _∨'_ ; _∧_ to _∧'_
               ; ∨-assoc to L-∨-assoc ; ∨-comm to L-∨-comm
               ; ∧-assoc to L-∧-assoc ; ∧-comm to L-∧-comm
               ; ∨-absorbs-∧ to L-∨-absorbs-∧ ; ∧-absorbs-∨ to L-∧-absorbs-∨
               ; ∧-distribˡ-∨ to L-∧-distribˡ-∨ ; ∨-distribˡ-∧ to L-∨-distribˡ-∧ )
  open Setoid setoid using ( _≈_ ) renaming ( refl to ≈refl ; trans to ≈trans ; sym to ≈sym )

  ∧-idem-derived : ∀ x → x ∧' x ≈ x
  ∧-idem-derived x = ≈trans (∧-cong ≈refl (≈sym (L-∨-absorbs-∧ x x))) (L-∧-absorbs-∨ x (x ∧' x))

  ∨-idem-derived : ∀ x → x ∨' x ≈ x
  ∨-idem-derived x = ≈trans (∨-cong ≈refl (≈sym (L-∧-absorbs-∨ x x))) (L-∨-absorbs-∧ x (x ∨' x))

  absorbʳ-derived : ∀ x y → (x ∧' y) ∨' x ≈ x
  absorbʳ-derived x y = ≈trans (L-∨-comm (x ∧' y) x) (L-∨-absorbs-∧ x y)

  𝑨 : Algebra _ _
  𝑨 = record { Domain = setoid ; Interp = interp }
    where
    interp : Func (⟨ Sig-Lattice ⟩ setoid) setoid
    interp ⟨$⟩ (∧-Op , args) = args 0F ∧' args 1F
    interp ⟨$⟩ (∨-Op , args) = args 0F ∨' args 1F
    cong interp {∧-Op , _} {.∧-Op , _} (refl , args≈) = ∧-cong (args≈ 0F) (args≈ 1F)
    cong interp {∨-Op , _} {.∨-Op , _} (refl , args≈) = ∨-cong (args≈ 0F) (args≈ 1F)

module _ {𝑫 : DistributiveLattice α ρ} where
  open DistributiveLattice-Op 𝑫
  open Setoid 𝔻[ proj₁ 𝑫 ] using ( _≈_ ) renaming ( refl to ≈refl )
  open DistributiveLattice-Op ⟪ ⟨ 𝑫 ⟩ᵈˡ ⟫ᵈˡ renaming ( _∧_ to _∧'_ ; _∨_ to _∨'_ )

  roundtrip-cbc-∧-dl : (a b : 𝕌[ proj₁ 𝑫 ]) → a ∧' b ≈ a ∧ b
  roundtrip-cbc-∧-dl a b = ≈refl

  roundtrip-cbc-∨-dl : (a b : 𝕌[ proj₁ 𝑫 ]) → a ∨' b ≈ a ∨ b
  roundtrip-cbc-∨-dl a b = ≈refl

module _ {L : stdlib-DistributiveLattice α ρ} where
  open stdlib-DistributiveLattice L using ( _≈_ ; _∧_ ; _∨_ ) renaming ( Carrier to A ; refl to ≈refl )
  open stdlib-DistributiveLattice ⟨ ⟪ L ⟫ᵈˡ ⟩ᵈˡ using () renaming ( _∧_ to _∧'_ ; _∨_ to _∨'_ )

  roundtrip-bcb-∧-dl : (a b : A) → (a ∧ b) ≈ (a ∧' b)
  roundtrip-bcb-∧-dl a b = ≈refl

  roundtrip-bcb-∨-dl : (a b : A) → (a ∨ b) ≈ (a ∨' b)
  roundtrip-bcb-∨-dl a b = ≈refl
```
