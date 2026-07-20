---
layout: default
file: "src/Classical/Structures/Ring.lagda.md"
title: "Classical.Structures.Ring module"
date: "2026-05-30"
author: "the agda-algebras development team"
---

### Rings {#classical-structures-ring}

This is the [Classical.Structures.Ring][] module of the [Agda Universal Algebra Library][].

A **ring** inhabits the Σ-typed structure `Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ Th-Ring` over
`Sig-Ring`.  Ring is the first structure in the [`Classical/`][Classical] tree with
*two* forgetful reducts that land in *different* structures: the additive triple
`(+-Op, 0-Op, -Op)` reducts to an [`AbelianGroup`][Classical.Structures.Group.AbelianGroup]
(`ring→abelianGroup`), and the multiplicative pair `(·-Op, 1-Op)` reducts to a
[`Monoid`][Classical.Structures.Monoid] (`ring→monoid`).  Both are container-morphism
reducts with identity position maps, discharging their target theory on the reduct by
the curried-law-pivot pattern of `monoid→semigroup` / `group→monoid`.

This module follows the [Lattice][Classical.Structures.Lattice] precedent of factoring
*every* defining equation into a standalone curried-form lemma in a
`module _ (𝑹 : Ring α ρ)` block (the `rg-*` family) above the forgetfuls, so that
`Ring-Op` and both reduct discharges consume one proof per law.  The additive `rg-+-*`
lemmas are the [`Group`][Classical.Structures.Group]/`AbelianGroup` laws re-derived
over `Sig-Ring`'s additive symbols; the multiplicative `rg-·-*` lemmas are the
`Monoid` laws over its multiplicative symbols; and `rg-distribˡ` / `rg-distribʳ` are
the two cross-operation laws, whose terms nest `·-Op` and `+-Op` and so bridge through
two single-symbol `interp-cong` compositions, exactly as Lattice's absorption laws do.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Ring where

open import Agda.Primitive                          using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -----------------------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Function                               using ( Func )
open import Level                                  using ( Level ; _⊔_ ; suc )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  as ≡ using ( _≡_ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open Func renaming ( to to _⟨$⟩_ )

-- Imports from the Agda Universal Algebra Library --------------------------------
open import Classical.Operations                    using ( pair ; Curry₂ ; Curry₁ ; Curry₀ )
open import Classical.Signatures.Group              using ( Sig-Group ; Op-Group )
                                                    renaming ( ∙-Op to ∙-Opᵍ ; ε-Op to ε-Opᵍ ; ⁻¹-Op to ⁻¹-Opᵍ )
open import Classical.Signatures.Monoid             using ( Sig-Monoid ; Op-Monoid )
                                                    renaming ( ∙-Op to ∙-Opᵐ ; ε-Op to ε-Opᵐ )
open import Classical.Signatures.Ring               using ( Sig-Ring ; Op-Ring ; +-Op ; 0-Op ; -Op ; ·-Op ; 1-Op )
open import Classical.Structures.Interpret          using ( interp-cong )
open import Setoid.Algebras.Reduct                  using ( reductBy )
open import Classical.Structures.Group.AbelianGroup using ( AbelianGroup ; _⊨ᵃᵍ_ )
open import Classical.Structures.Monoid             using ( Monoid ; _⊨ᵐᵒ_ )
open import Classical.Theories.Ring                 using ( Eq-Ring ; Th-Ring
                                                          ; +-assoc ; +-idˡ ; +-idʳ ; +-invˡ ; +-invʳ ; +-comm
                                                          ; ·-assoc ; ·-idˡ ; ·-idʳ ; distribˡ ; distribʳ )
open import Classical.Theories.AbelianGroup         using ( Th-AbelianGroup )
                                                    renaming ( assoc to assocᵃ ; idˡ to idˡᵃ ; idʳ to idʳᵃ
                                                             ; invˡ to invˡᵃ ; invʳ to invʳᵃ ; comm to commᵃ )
open import Classical.Theories.Monoid               using ( Th-Monoid )
                                                    renaming ( assoc to assocᵐ ; idˡ to idˡᵐ ; idʳ to idʳᵐ )
open import Overture.Terms                          using ( Term ; ℊ ; node )
open import Overture.Signatures                     using ( ArityOf ; OperationSymbolsOf )
open import Setoid.Algebras.Basic                   using ( Algebra ; _^_ ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Terms                            using ( module Environment )

open import Setoid.Varieties.EquationalLogic using ( _⊧_≈_ )

private variable α ρ : Level
```
-->

#### The local satisfaction predicate

```agda
infix 4 _⊨ʳᵍ_
_⊨ʳᵍ_ : (𝑨 : Algebra {𝑆 = Sig-Ring} α ρ) (ℰ : Eq-Ring → Term (Fin 3) × Term (Fin 3)) → Type (α ⊔ ρ)
𝑨 ⊨ʳᵍ ℰ = ∀ i → 𝑨 ⊧ proj₁ (ℰ i) ≈ proj₂ (ℰ i)
```

#### The type of rings

```agda
Ring : (α ρ : Level) → Type (suc α ⊔ suc ρ)
Ring α ρ = Σ[ 𝑨 ∈ Algebra {𝑆 = Sig-Ring} α ρ ] 𝑨 ⊨ʳᵍ Th-Ring
```

#### The additive and multiplicative reduct algebras

The container morphism `Sig-Group ⟹ Sig-Ring` sends `(∙-Opᵍ, ε-Opᵍ, ⁻¹-Opᵍ)` to the
additive `(+-Op, 0-Op, -Op)`; the morphism `Sig-Monoid ⟹ Sig-Ring` sends
`(∙-Opᵐ, ε-Opᵐ)` to the multiplicative `(·-Op, 1-Op)`.  Both position maps are the
identity.

```agda
+-incl : Op-Group → Op-Ring
+-incl ∙-Opᵍ  = +-Op
+-incl ε-Opᵍ  = 0-Op
+-incl ⁻¹-Opᵍ = -Op

+-κ : (o : OperationSymbolsOf Sig-Group) → ArityOf Sig-Ring (+-incl o) → ArityOf Sig-Group o
+-κ ∙-Opᵍ  = λ z → z
+-κ ε-Opᵍ  = λ z → z
+-κ ⁻¹-Opᵍ = λ z → z

·-incl : Op-Monoid → Op-Ring
·-incl ∙-Opᵐ = ·-Op
·-incl ε-Opᵐ = 1-Op

·-κ : (o : OperationSymbolsOf Sig-Monoid) → ArityOf Sig-Ring (·-incl o) → ArityOf Sig-Monoid o
·-κ ∙-Opᵐ = λ z → z
·-κ ε-Opᵐ = λ z → z

ring→abelianGroupAlg : Ring α ρ → Algebra {𝑆 = Sig-Group} α ρ
ring→abelianGroupAlg 𝑹 = reductBy +-incl +-κ (𝑹 .proj₁)

ring→monoidAlg : Ring α ρ → Algebra {𝑆 = Sig-Monoid} α ρ
ring→monoidAlg 𝑹 = reductBy ·-incl ·-κ (𝑹 .proj₁)
```

#### The eleven curried laws, standalone

Each `Th-Ring` equation is proved here in curried form once, above the forgetfuls.
The pattern is the same throughout: bridge each `node` to curried form via
`interp-cong`, apply the satisfaction-witness equation, refold.

```agda
module _ (ℛ : Ring α ρ) where
  private 𝑹 = proj₁ ℛ
  open Setoid 𝔻[ 𝑹 ]
  open Environment 𝑹 using ( ⟦_⟧ )
  open SetoidReasoning 𝔻[ 𝑹 ]

  private
    infixl 6 _+_
    infixl 7 _·_
    infix  8 -_

    -- nullary ops
    0R 1R : 𝕌[ 𝑹 ]
    0R = Curry₀ (0-Op ^ 𝑹)
    1R = Curry₀ (1-Op ^ 𝑹)

    -- unary ops
    -_ : 𝕌[ 𝑹 ] → 𝕌[ 𝑹 ]
    -_ = Curry₁ (-Op ^ 𝑹)

    -- binary ops
    _+_ _·_ : 𝕌[ 𝑹 ] → 𝕌[ 𝑹 ] → 𝕌[ 𝑹 ]
    _+_ = Curry₂ (+-Op ^ 𝑹)
    _·_ = Curry₂ (·-Op ^ 𝑹)

    +-cong : ∀ {x y u v} → x ≈ y → u ≈ v → (x + u) ≈ (y + v)
    +-cong x≈y u≈v = interp-cong 𝑹 +-Op (λ { 0F → x≈y ; 1F → u≈v })

    ·-cong : ∀ {x y u v} → x ≈ y → u ≈ v → (x · u) ≈ (y · v)
    ·-cong x≈y u≈v = interp-cong 𝑹 ·-Op (λ { 0F → x≈y ; 1F → u≈v })

    neg-cong : ∀ {x y} → x ≈ y → (- x) ≈ (- y)
    neg-cong x≈y = interp-cong 𝑹 -Op (λ { 0F → x≈y })

    i+ : (s t : Term (Fin 3)) (η : Fin 3 → 𝕌[ 𝑹 ])
       → ⟦ node +-Op (pair s t) ⟧ ⟨$⟩ η ≈ ⟦ s ⟧ ⟨$⟩ η + ⟦ t ⟧ ⟨$⟩ η
    i+ s t η = interp-cong 𝑹 +-Op (λ { 0F → refl ; 1F → refl })

    i· : (s t : Term (Fin 3)) (η : Fin 3 → 𝕌[ 𝑹 ])
       → ⟦ node ·-Op (pair s t) ⟧ ⟨$⟩ η ≈ ⟦ s ⟧ ⟨$⟩ η · ⟦ t ⟧ ⟨$⟩ η
    i· s t η = interp-cong 𝑹 ·-Op (λ { 0F → refl ; 1F → refl })

    i0 : (η : Fin 3 → 𝕌[ 𝑹 ]) → ⟦ node 0-Op (λ ()) ⟧ ⟨$⟩ η ≈ 0R
    i0 η = interp-cong 𝑹 0-Op (λ ())

    i1 : (η : Fin 3 → 𝕌[ 𝑹 ]) → ⟦ node 1-Op (λ ()) ⟧ ⟨$⟩ η ≈ 1R
    i1 η = interp-cong 𝑹 1-Op (λ ())

    i- : (s : Term (Fin 3)) (η : Fin 3 → 𝕌[ 𝑹 ])
       → ⟦ node -Op (λ _ → s) ⟧ ⟨$⟩ η ≈ - ⟦ s ⟧ ⟨$⟩ η
    i- s η = interp-cong 𝑹 -Op (λ { 0F → refl })

  -- Additive associativity
  rg-+-assoc : ∀ x y z → x + y + z ≈ x + (y + z)
  rg-+-assoc x y z = begin
    x + y + z         ≈⟨ +-cong (sym (i+ (ℊ 0F) (ℊ 1F) η)) refl ⟩
    ⟦ xy ⟧ ⟨$⟩ η + z  ≈⟨ sym (i+ xy (ℊ 2F) η) ⟩
    ⟦ lhsT ⟧ ⟨$⟩ η    ≈⟨ proj₂ ℛ +-assoc η ⟩
    ⟦ rhsT ⟧ ⟨$⟩ η    ≈⟨ i+ (ℊ 0F) yz η ⟩
    x + ⟦ yz ⟧ ⟨$⟩ η  ≈⟨ +-cong refl (i+ (ℊ 1F) (ℊ 2F) η) ⟩
    x + (y + z)       ∎
    where
    η : Fin 3 → 𝕌[ 𝑹 ]
    η = λ { 0F → x ; 1F → y ; 2F → z }
    xy yz lhsT rhsT : Term (Fin 3)
    xy   = node +-Op (pair (ℊ 0F) (ℊ 1F))
    yz   = node +-Op (pair (ℊ 1F) (ℊ 2F))
    lhsT = node +-Op (pair xy (ℊ 2F))
    rhsT = node +-Op (pair (ℊ 0F) yz)

  -- Additive identities
  rg-+-idˡ : ∀ x → 0R + x ≈ x
  rg-+-idˡ x = begin
    0R + x                          ≈⟨ +-cong (sym (i0 η)) refl ⟩
    ⟦ node 0-Op (λ ()) ⟧ ⟨$⟩ η + x  ≈⟨ sym (i+ (node 0-Op (λ ())) (ℊ 0F) η) ⟩
    ⟦ lhsT ⟧ ⟨$⟩ η                  ≈⟨ proj₂ ℛ +-idˡ η ⟩
    x                               ∎
    where
    η : Fin 3 → 𝕌[ 𝑹 ]
    η = λ { 0F → x ; 1F → x ; 2F → x }
    lhsT : Term (Fin 3)
    lhsT = node +-Op (pair (node 0-Op (λ ())) (ℊ 0F))

  rg-+-idʳ : ∀ x → x + 0R ≈ x
  rg-+-idʳ x = begin
    x + 0R                          ≈⟨ +-cong refl (sym (i0 η)) ⟩
    x + ⟦ node 0-Op (λ ()) ⟧ ⟨$⟩ η  ≈⟨ sym (i+ (ℊ 0F) (node 0-Op (λ ())) η) ⟩
    ⟦ lhsT ⟧ ⟨$⟩ η                  ≈⟨ proj₂ ℛ +-idʳ η ⟩
    x                               ∎
    where
    η : Fin 3 → 𝕌[ 𝑹 ]
    η = λ { 0F → x ; 1F → x ; 2F → x }
    lhsT : Term (Fin 3)
    lhsT = node +-Op (pair (ℊ 0F) (node 0-Op (λ ())))

  -- Additive inverses
  rg-+-invˡ : ∀ x → (- x) + x ≈ 0R
  rg-+-invˡ x = begin
    (- x) + x                   ≈⟨ +-cong (sym (i- (ℊ 0F) η)) refl ⟩
    ⟦ negT ⟧ ⟨$⟩ η + x          ≈⟨ sym (i+ negT (ℊ 0F) η) ⟩
    ⟦ lhsT ⟧ ⟨$⟩ η              ≈⟨ proj₂ ℛ +-invˡ η ⟩
    ⟦ node 0-Op (λ ()) ⟧ ⟨$⟩ η  ≈⟨ i0 η ⟩
    0R                          ∎
    where
    η : Fin 3 → 𝕌[ 𝑹 ]
    η = λ { 0F → x ; 1F → x ; 2F → x }
    negT lhsT : Term (Fin 3)
    negT = node -Op (λ _ → ℊ 0F)
    lhsT = node +-Op (pair negT (ℊ 0F))

  rg-+-invʳ : ∀ x → x + (- x) ≈ 0R
  rg-+-invʳ x = begin
    x + (- x)                   ≈⟨ +-cong refl (sym (i- (ℊ 0F) η)) ⟩
    x + ⟦ negT ⟧ ⟨$⟩ η          ≈⟨ sym (i+ (ℊ 0F) negT η) ⟩
    ⟦ lhsT ⟧ ⟨$⟩ η              ≈⟨ proj₂ ℛ +-invʳ η ⟩
    ⟦ node 0-Op (λ ()) ⟧ ⟨$⟩ η  ≈⟨ i0 η ⟩
    0R                          ∎
    where
    η : Fin 3 → 𝕌[ 𝑹 ]
    η = λ { 0F → x ; 1F → x ; 2F → x }
    negT lhsT : Term (Fin 3)
    negT = node -Op (λ _ → ℊ 0F)
    lhsT = node +-Op (pair (ℊ 0F) negT)

  -- Additive commutativity
  rg-+-comm : ∀ x y → x + y ≈ y + x
  rg-+-comm x y = begin
    x + y         ≈⟨ sym (i+ (ℊ 0F) (ℊ 1F) η) ⟩
    ⟦ xy ⟧ ⟨$⟩ η  ≈⟨ proj₂ ℛ +-comm η ⟩
    ⟦ yx ⟧ ⟨$⟩ η  ≈⟨ i+ (ℊ 1F) (ℊ 0F) η ⟩
    y + x         ∎
    where
    η : Fin 3 → 𝕌[ 𝑹 ]
    η = λ { 0F → x ; 1F → y ; 2F → x }
    xy yx : Term (Fin 3)
    xy = node +-Op (pair (ℊ 0F) (ℊ 1F))
    yx = node +-Op (pair (ℊ 1F) (ℊ 0F))

  -- Multiplicative associativity
  rg-·-assoc : ∀ x y z → x · y · z ≈ x · (y · z)
  rg-·-assoc x y z = begin
    x · y · z         ≈⟨ ·-cong (sym (i· (ℊ 0F) (ℊ 1F) η)) refl ⟩
    ⟦ xy ⟧ ⟨$⟩ η · z  ≈⟨ sym (i· xy (ℊ 2F) η) ⟩
    ⟦ lhsT ⟧ ⟨$⟩ η    ≈⟨ proj₂ ℛ ·-assoc η ⟩
    ⟦ rhsT ⟧ ⟨$⟩ η    ≈⟨ i· (ℊ 0F) yz η ⟩
    x · ⟦ yz ⟧ ⟨$⟩ η  ≈⟨ ·-cong refl (i· (ℊ 1F) (ℊ 2F) η) ⟩
    x · (y · z)       ∎
    where
    η : Fin 3 → 𝕌[ 𝑹 ]
    η = λ { 0F → x ; 1F → y ; 2F → z }
    xy yz lhsT rhsT : Term (Fin 3)
    xy   = node ·-Op (pair (ℊ 0F) (ℊ 1F))
    yz   = node ·-Op (pair (ℊ 1F) (ℊ 2F))
    lhsT = node ·-Op (pair xy (ℊ 2F))
    rhsT = node ·-Op (pair (ℊ 0F) yz)

  -- Multiplicative identities
  rg-·-idˡ : ∀ x → 1R · x ≈ x
  rg-·-idˡ x = begin
    1R · x                          ≈⟨ ·-cong (sym (i1 η)) refl ⟩
    ⟦ node 1-Op (λ ()) ⟧ ⟨$⟩ η · x  ≈⟨ sym (i· (node 1-Op (λ ())) (ℊ 0F) η) ⟩
    ⟦ lhsT ⟧ ⟨$⟩ η                  ≈⟨ proj₂ ℛ ·-idˡ η ⟩
    x                               ∎
    where
    η : Fin 3 → 𝕌[ 𝑹 ]
    η = λ { 0F → x ; 1F → x ; 2F → x }
    lhsT : Term (Fin 3)
    lhsT = node ·-Op (pair (node 1-Op (λ ())) (ℊ 0F))

  rg-·-idʳ : ∀ x → x · 1R ≈ x
  rg-·-idʳ x = begin
    x · 1R                          ≈⟨ ·-cong refl (sym (i1 η)) ⟩
    x · ⟦ node 1-Op (λ ()) ⟧ ⟨$⟩ η  ≈⟨ sym (i· (ℊ 0F) (node 1-Op (λ ())) η) ⟩
    ⟦ lhsT ⟧ ⟨$⟩ η                  ≈⟨ proj₂ ℛ ·-idʳ η ⟩
    x                               ∎
    where
    η : Fin 3 → 𝕌[ 𝑹 ]
    η = λ { 0F → x ; 1F → x ; 2F → x }
    lhsT : Term (Fin 3)
    lhsT = node ·-Op (pair (ℊ 0F) (node 1-Op (λ ())))

  -- Left distributivity
  rg-distribˡ : ∀ x y z → x · (y + z) ≈ x · y + x · z
  rg-distribˡ x y z = begin
    x · (y + z)                  ≈⟨ ·-cong refl (sym (i+ (ℊ 1F) (ℊ 2F) η)) ⟩
    x · ⟦ y+z ⟧ ⟨$⟩ η            ≈⟨ sym (i· (ℊ 0F) y+z η) ⟩
    ⟦ lhsT ⟧ ⟨$⟩ η               ≈⟨ proj₂ ℛ distribˡ η ⟩
    ⟦ rhsT ⟧ ⟨$⟩ η               ≈⟨ i+ xy xz η ⟩
    ⟦ xy ⟧ ⟨$⟩ η + ⟦ xz ⟧ ⟨$⟩ η  ≈⟨ +-cong (i· (ℊ 0F) (ℊ 1F) η) (i· (ℊ 0F) (ℊ 2F) η) ⟩
    x · y + x · z        ∎
    where
    η : Fin 3 → 𝕌[ 𝑹 ]
    η = λ { 0F → x ; 1F → y ; 2F → z }
    y+z xy xz lhsT rhsT : Term (Fin 3)
    y+z  = node +-Op (pair (ℊ 1F) (ℊ 2F))
    xy   = node ·-Op (pair (ℊ 0F) (ℊ 1F))
    xz   = node ·-Op (pair (ℊ 0F) (ℊ 2F))
    lhsT = node ·-Op (pair (ℊ 0F) y+z)
    rhsT = node +-Op (pair xy xz)

  -- Right distributivity
  rg-distribʳ : ∀ x y z → (y + z) · x ≈ y · x + z · x
  rg-distribʳ x y z = begin
    (y + z) · x                  ≈⟨ ·-cong (sym (i+ (ℊ 1F) (ℊ 2F) η)) refl ⟩
    ⟦ y+z ⟧ ⟨$⟩ η · x            ≈⟨ sym (i· y+z (ℊ 0F) η) ⟩
    ⟦ lhsT ⟧ ⟨$⟩ η               ≈⟨ proj₂ ℛ distribʳ η ⟩
    ⟦ rhsT ⟧ ⟨$⟩ η               ≈⟨ i+ yx zx η ⟩
    ⟦ yx ⟧ ⟨$⟩ η + ⟦ zx ⟧ ⟨$⟩ η  ≈⟨ +-cong (i· (ℊ 1F) (ℊ 0F) η) (i· (ℊ 2F) (ℊ 0F) η) ⟩
    y · x + z · x                ∎
    where
    η : Fin 3 → 𝕌[ 𝑹 ]
    η = λ { 0F → x ; 1F → y ; 2F → z }
    y+z yx zx lhsT rhsT : Term (Fin 3)
    y+z  = node +-Op (pair (ℊ 1F) (ℊ 2F))
    yx   = node ·-Op (pair (ℊ 1F) (ℊ 0F))
    zx   = node ·-Op (pair (ℊ 2F) (ℊ 0F))
    lhsT = node ·-Op (pair y+z (ℊ 0F))
    rhsT = node +-Op (pair yx zx)
```

#### The `Ring-Op` module

`Ring-Op` exposes the additive `(_+_, 0R, -_)`, the multiplicative `(_·_, 1R)`, their
congruences and node-bridges, the eleven curried laws, and the satisfaction-witness
`equations` accessor.

```agda
module Ring-Op {α ρ : Level} (ℛ : Ring α ρ) where
  private 𝑹 = proj₁ ℛ
  open Setoid 𝔻[ 𝑹 ]
  open Environment 𝑹 using ( ⟦_⟧ )

  infixl 6 _+_
  infixl 7 _·_
  infix  8 -_

  -- nullary ops
  0R 1R : 𝕌[ 𝑹 ]
  0R = Curry₀ (0-Op ^ 𝑹)
  1R = Curry₀ (1-Op ^ 𝑹)

  -- unary ops
  -_ : 𝕌[ 𝑹 ] → 𝕌[ 𝑹 ]
  -_ = Curry₁ (-Op ^ 𝑹)

  -- binary ops
  _+_ _·_ : 𝕌[ 𝑹 ] → 𝕌[ 𝑹 ] → 𝕌[ 𝑹 ]
  _+_ = Curry₂ (+-Op ^ 𝑹)
  _·_ = Curry₂ (·-Op ^ 𝑹)

  equations : 𝑹 ⊨ʳᵍ Th-Ring
  equations = proj₂ ℛ

  +-cong : ∀ {x y u v} → x ≈ y → u ≈ v → x + u ≈ y + v
  +-cong x≈y u≈v = interp-cong 𝑹 +-Op (λ { 0F → x≈y ; 1F → u≈v })
  ·-cong : ∀ {x y u v} → x ≈ y → u ≈ v → x · u ≈ y · v
  ·-cong x≈y u≈v = interp-cong 𝑹 ·-Op (λ { 0F → x≈y ; 1F → u≈v })
  neg-cong : ∀ {x y} → x ≈ y → - x ≈ - y
  neg-cong x≈y = interp-cong 𝑹 -Op (λ { 0F → x≈y })

  interp-node-+ : (s t : Term (Fin 3)) {η : Fin 3 → 𝕌[ 𝑹 ]}
    → ⟦ node +-Op (pair s t) ⟧ ⟨$⟩ η ≈ ⟦ s ⟧ ⟨$⟩ η + ⟦ t ⟧ ⟨$⟩ η
  interp-node-+ s t = interp-cong 𝑹 +-Op (λ { 0F → refl ; 1F → refl })

  interp-node-· : (s t : Term (Fin 3)) {η : Fin 3 → 𝕌[ 𝑹 ]}
    → ⟦ node ·-Op (pair s t) ⟧ ⟨$⟩ η ≈ ⟦ s ⟧ ⟨$⟩ η · ⟦ t ⟧ ⟨$⟩ η
  interp-node-· s t = interp-cong 𝑹 ·-Op (λ { 0F → refl ; 1F → refl })

  interp-node-0 : {η : Fin 3 → 𝕌[ 𝑹 ]} → ⟦ node 0-Op (λ ()) ⟧ ⟨$⟩ η ≈ 0R
  interp-node-0 = interp-cong 𝑹 0-Op (λ ())

  interp-node-1 : {η : Fin 3 → 𝕌[ 𝑹 ]} → ⟦ node 1-Op (λ ()) ⟧ ⟨$⟩ η ≈ 1R
  interp-node-1 = interp-cong 𝑹 1-Op (λ ())

  interp-node-neg : (s : Term (Fin 3)) {η : Fin 3 → 𝕌[ 𝑹 ]}
    → ⟦ node -Op (λ _ → s) ⟧ ⟨$⟩ η ≈ - ⟦ s ⟧ ⟨$⟩ η
  interp-node-neg s = interp-cong 𝑹 -Op (λ { 0F → refl })

  +-assoc-law : ∀ x y z → (x + y) + z ≈ x + (y + z)
  +-assoc-law = rg-+-assoc ℛ
  +-idˡ-law : ∀ x → 0R + x ≈ x
  +-idˡ-law = rg-+-idˡ ℛ
  +-idʳ-law : ∀ x → x + 0R ≈ x
  +-idʳ-law = rg-+-idʳ ℛ
  +-invˡ-law : ∀ x → (- x) + x ≈ 0R
  +-invˡ-law = rg-+-invˡ ℛ
  +-invʳ-law : ∀ x → x + (- x) ≈ 0R
  +-invʳ-law = rg-+-invʳ ℛ
  +-comm-law : ∀ x y → x + y ≈ y + x
  +-comm-law = rg-+-comm ℛ
  ·-assoc-law : ∀ x y z → (x · y) · z ≈ x · (y · z)
  ·-assoc-law = rg-·-assoc ℛ
  ·-idˡ-law : ∀ x → 1R · x ≈ x
  ·-idˡ-law = rg-·-idˡ ℛ
  ·-idʳ-law : ∀ x → x · 1R ≈ x
  ·-idʳ-law = rg-·-idʳ ℛ
  distribˡ-law : ∀ x y z → x · (y + z) ≈ (x · y) + (x · z)
  distribˡ-law = rg-distribˡ ℛ
  distribʳ-law : ∀ x y z → (y + z) · x ≈ (y · x) + (z · x)
  distribʳ-law = rg-distribʳ ℛ
```

#### The forgetful projection to abelian groups

`ring→abelianGroup` takes a ring to the abelian group on its additive reduct,
discharging the six `Th-AbelianGroup` equations on `ring→abelianGroupAlg` via
`Ring-Op`'s additive curried laws.

```agda
ring→abelianGroup : Ring α ρ → AbelianGroup α ρ
ring→abelianGroup ℛ@(𝑹 , _) = 𝑹ᵍ , thm
  where
  𝑹ᵍ : Algebra {𝑆 = Sig-Group} _ _
  𝑹ᵍ = ring→abelianGroupAlg ℛ
  open Setoid 𝔻[ 𝑹 ]
  open Environment 𝑹ᵍ using ( ⟦_⟧ )
  open SetoidReasoning 𝔻[ 𝑹 ]
  open Ring-Op ℛ using ( _+_ ; 0R ; -_ ; +-cong ; neg-cong
                       ; +-assoc-law ; +-idˡ-law ; +-idʳ-law ; +-invˡ-law ; +-invʳ-law ; +-comm-law )

  i+ : (s t : Term (Fin 3)) (η : Fin 3 → 𝕌[ 𝑹 ])
     → ⟦ node ∙-Opᵍ (pair s t) ⟧ ⟨$⟩ η ≈ (⟦ s ⟧ ⟨$⟩ η) + (⟦ t ⟧ ⟨$⟩ η)
  i+ s t η = interp-cong 𝑹ᵍ ∙-Opᵍ (λ { 0F → refl ; 1F → refl })
  i0 : (η : Fin 3 → 𝕌[ 𝑹 ]) → ⟦ node ε-Opᵍ (λ ()) ⟧ ⟨$⟩ η ≈ 0R
  i0 η = interp-cong 𝑹ᵍ ε-Opᵍ (λ ())
  i- : (s : Term (Fin 3)) (η : Fin 3 → 𝕌[ 𝑹 ])
     → ⟦ node ⁻¹-Opᵍ (λ _ → s) ⟧ ⟨$⟩ η ≈ - (⟦ s ⟧ ⟨$⟩ η)
  i- s η = interp-cong 𝑹ᵍ ⁻¹-Opᵍ (λ { 0F → refl })

  thm : 𝑹ᵍ ⊨ᵃᵍ Th-AbelianGroup
  thm assocᵃ η = begin
    ⟦ Th-AbelianGroup assocᵃ .proj₁ ⟧ ⟨$⟩ η  ≈⟨ i+ xy (ℊ 2F) η ⟩
    ⟦ xy ⟧ ⟨$⟩ η + z                         ≈⟨ +-cong (i+ (ℊ 0F) (ℊ 1F) η) refl ⟩
    x + y + z                                ≈⟨ +-assoc-law x y z ⟩
    x + (y + z)                              ≈˘⟨ +-cong refl (i+ (ℊ 1F) (ℊ 2F) η) ⟩
    x + ⟦ yz ⟧ ⟨$⟩ η                         ≈˘⟨ i+ (ℊ 0F) yz η ⟩
    ⟦ Th-AbelianGroup assocᵃ .proj₂ ⟧ ⟨$⟩ η  ∎
    where
    x y z : 𝕌[ 𝑹 ]
    x = η 0F ; y = η 1F ; z = η 2F
    xy yz : Term (Fin 3)
    xy = node ∙-Opᵍ (pair (ℊ 0F) (ℊ 1F))
    yz = node ∙-Opᵍ (pair (ℊ 1F) (ℊ 2F))
  thm idˡᵃ η = let x = η 0F in begin
    ⟦ Th-AbelianGroup idˡᵃ .proj₁ ⟧ ⟨$⟩ η  ≈⟨ i+ (node ε-Opᵍ (λ ())) (ℊ 0F) η ⟩
    ⟦ node ε-Opᵍ (λ ()) ⟧ ⟨$⟩ η + x        ≈⟨ +-cong (i0 η) refl ⟩
    0R + x                                 ≈⟨ +-idˡ-law x ⟩
    x                                      ∎
  thm idʳᵃ η = begin
    ⟦ Th-AbelianGroup idʳᵃ .proj₁ ⟧ ⟨$⟩ η  ≈⟨ i+ (ℊ 0F) (node ε-Opᵍ (λ ())) η ⟩
    _ + ⟦ node ε-Opᵍ (λ ()) ⟧ ⟨$⟩ η        ≈⟨ +-cong refl (i0 η) ⟩
    _ + 0R                                 ≈⟨ +-idʳ-law _ ⟩
    _                                      ∎
  thm invˡᵃ η = begin
    ⟦ Th-AbelianGroup invˡᵃ .proj₁ ⟧ ⟨$⟩ η  ≈⟨ i+ negT (ℊ 0F) η ⟩
    ⟦ negT ⟧ ⟨$⟩ η + _                      ≈⟨ +-cong (i- (ℊ 0F) η) refl ⟩
    (- _) + _                               ≈⟨ +-invˡ-law _ ⟩
    0R                                      ≈˘⟨ i0 η ⟩
    ⟦ Th-AbelianGroup invˡᵃ .proj₂ ⟧ ⟨$⟩ η  ∎
    where negT : Term (Fin 3)
          negT = node ⁻¹-Opᵍ (λ _ → ℊ 0F)
  thm invʳᵃ η = begin
    ⟦ Th-AbelianGroup invʳᵃ .proj₁ ⟧ ⟨$⟩ η  ≈⟨ i+ (ℊ 0F) negT η ⟩
    _ + ⟦ negT ⟧ ⟨$⟩ η                      ≈⟨ +-cong refl (i- (ℊ 0F) η) ⟩
    _ + (- _)                               ≈⟨ +-invʳ-law _ ⟩
    0R                                      ≈˘⟨ i0 η ⟩
    ⟦ Th-AbelianGroup invʳᵃ .proj₂ ⟧ ⟨$⟩ η  ∎
    where
    negT : Term (Fin 3)
    negT = node ⁻¹-Opᵍ (λ _ → ℊ 0F)
  thm commᵃ η = begin
    ⟦ Th-AbelianGroup commᵃ .proj₁ ⟧ ⟨$⟩ η   ≈⟨ i+ (ℊ 0F) (ℊ 1F) η ⟩
    _ + _                                    ≈⟨ +-comm-law _ _ ⟩
    _ + _                                    ≈˘⟨ i+ (ℊ 1F) (ℊ 0F) η ⟩
    ⟦ Th-AbelianGroup commᵃ .proj₂ ⟧ ⟨$⟩ η   ∎
```

#### The forgetful projection to monoids

`ring→monoid` takes a ring to the monoid on its multiplicative reduct, discharging the
three `Th-Monoid` equations on `ring→monoidAlg` via `Ring-Op`'s multiplicative
curried laws.

```agda
ring→monoid : Ring α ρ → Monoid α ρ
ring→monoid ℛ@(𝑹 , _) = 𝑹-mon , thm
  where
  𝑹-mon : Algebra {𝑆 = Sig-Monoid} _ _
  𝑹-mon = ring→monoidAlg ℛ
  open Setoid 𝔻[ 𝑹 ]
  open Environment 𝑹-mon using ( ⟦_⟧ )
  open SetoidReasoning 𝔻[ 𝑹 ]
  open Ring-Op ℛ using ( _·_ ; 1R ; ·-cong ; ·-assoc-law ; ·-idˡ-law ; ·-idʳ-law )

  i· : {s t : Term (Fin 3)} {η : Fin 3 → 𝕌[ 𝑹 ]}
     → ⟦ node ∙-Opᵐ (pair s t) ⟧ ⟨$⟩ η ≈ (⟦ s ⟧ ⟨$⟩ η) · (⟦ t ⟧ ⟨$⟩ η)
  i· = interp-cong 𝑹-mon ∙-Opᵐ (λ { 0F → refl ; 1F → refl })
  i1 : {η : Fin 3 → 𝕌[ 𝑹 ]} → ⟦ node ε-Opᵐ (λ ()) ⟧ ⟨$⟩ η ≈ 1R
  i1 = interp-cong 𝑹-mon ε-Opᵐ (λ ())

  thm : 𝑹-mon ⊨ᵐᵒ Th-Monoid
  thm assocᵐ η = begin
    ⟦ Th-Monoid assocᵐ .proj₁ ⟧ ⟨$⟩ η  ≈⟨ i· ⟩
    ⟦ xy ⟧ ⟨$⟩ η · z                   ≈⟨ ·-cong i·  refl ⟩
    x · y · z                          ≈⟨ ·-assoc-law x y z ⟩
    x · (y · z)                        ≈˘⟨ ·-cong refl i· ⟩
    x · ⟦ yz ⟧ ⟨$⟩ η                   ≈˘⟨ i·  ⟩
    ⟦ Th-Monoid assocᵐ .proj₂ ⟧ ⟨$⟩ η  ∎
    where
    x y z : 𝕌[ 𝑹-mon ]
    x = η 0F ; y = η 1F ; z = η 2F
    xy yz : Term (Fin 3)
    xy = node ∙-Opᵐ (pair (ℊ 0F) (ℊ 1F))
    yz = node ∙-Opᵐ (pair (ℊ 1F) (ℊ 2F))
  thm idˡᵐ η = begin
    ⟦ Th-Monoid idˡᵐ .proj₁ ⟧ ⟨$⟩ η  ≈⟨ i· ⟩
    ⟦ node ε-Opᵐ (λ ()) ⟧ ⟨$⟩ η · _  ≈⟨ ·-cong i1 refl ⟩
    1R · _                           ≈⟨ ·-idˡ-law _ ⟩
    _                                ∎
  thm idʳᵐ η = begin
    ⟦ Th-Monoid idʳᵐ .proj₁ ⟧ ⟨$⟩ η  ≈⟨ i· ⟩
    _ · ⟦ node ε-Opᵐ (λ ()) ⟧ ⟨$⟩ η  ≈⟨ ·-cong refl i1 ⟩
    _ · 1R                           ≈⟨ ·-idʳ-law _ ⟩
    _                                ∎
```

#### Ring builders

`opsToBareRing` builds a "raw" `Sig-Ring`-algebra over `≡.setoid A` from a carrier and
the five operations.  `eqsToRing` adds the eleven equation proofs.

```agda
open Algebra

opsToBareRing : (A : Type α) (_+'_ : A → A → A) (0' : A) (-'_ : A → A)
  (_*'_ : A → A → A) (1' : A) → Algebra {𝑆 = Sig-Ring} α α
opsToBareRing A _ _ _ _ _    .Domain = ≡.setoid A
opsToBareRing A _+'_ _ _ _ _ .Interp ⟨$⟩ (+-Op , args) = args 0F +' args 1F
opsToBareRing A _ 0' _ _ _   .Interp ⟨$⟩ (0-Op , _)    = 0'
opsToBareRing A _ _ -'_ _ _  .Interp ⟨$⟩ (-Op , args)  = -' (args 0F)
opsToBareRing A _ _ _ _*'_ _ .Interp ⟨$⟩ (·-Op , args) = args 0F *' args 1F
opsToBareRing A _ _ _ _ 1'   .Interp ⟨$⟩ (1-Op , _)    = 1'
opsToBareRing A _+'_ _ _ _ _ .Interp .cong {+-Op , _} (≡.refl , u≈v) = ≡.cong₂ _+'_ (u≈v 0F) (u≈v 1F)
opsToBareRing A _ _ _ _ _    .Interp .cong {0-Op , _} (≡.refl , _)   = ≡.refl
opsToBareRing A _ _ -'_ _ _  .Interp .cong { -Op , _} (≡.refl , u≈v) = ≡.cong -'_ (u≈v 0F)
opsToBareRing A _ _ _ _*'_ _ .Interp .cong {·-Op , _} (≡.refl , u≈v) = ≡.cong₂ _*'_ (u≈v 0F) (u≈v 1F)
opsToBareRing A _ _ _ _ _    .Interp .cong {1-Op , _} (≡.refl , _)   = ≡.refl

eqsToRing : (A : Type α) (_+'_ : A → A → A) (0' : A) (-'_ : A → A) (_*'_ : A → A → A) (1' : A)
  → (+-assoc-≡ : ∀ a b c → (a +' b) +' c ≡ a +' (b +' c))
  → (+-idˡ-≡ : ∀ a → 0' +' a ≡ a) (+-idʳ-≡ : ∀ a → a +' 0' ≡ a)
  → (+-invˡ-≡ : ∀ a → (-' a) +' a ≡ 0') (+-invʳ-≡ : ∀ a → a +' (-' a) ≡ 0')
  → (+-comm-≡ : ∀ a b → a +' b ≡ b +' a)
  → (*-assoc-≡ : ∀ a b c → (a *' b) *' c ≡ a *' (b *' c))
  → (*-idˡ-≡ : ∀ a → 1' *' a ≡ a) (*-idʳ-≡ : ∀ a → a *' 1' ≡ a)
  → (distribˡ-≡ : ∀ a b c → a *' (b +' c) ≡ (a *' b) +' (a *' c))
  → (distribʳ-≡ : ∀ a b c → (b +' c) *' a ≡ (b *' a) +' (c *' a))
  → Ring α α
eqsToRing A _+'_ 0' -'_ _*'_ 1'
  +-assoc-≡ +-idˡ-≡ +-idʳ-≡ +-invˡ-≡ +-invʳ-≡ +-comm-≡ *-assoc-≡ *-idˡ-≡ *-idʳ-≡ distribˡ-≡ distribʳ-≡ =
  opsToBareRing A _+'_ 0' -'_ _*'_ 1' , proof
  where
  proof : opsToBareRing A _+'_ 0' -'_ _*'_ 1' ⊨ʳᵍ Th-Ring
  proof +-assoc  ρ = +-assoc-≡  (ρ 0F) (ρ 1F) (ρ 2F)
  proof +-idˡ    ρ = +-idˡ-≡    (ρ 0F)
  proof +-idʳ    ρ = +-idʳ-≡    (ρ 0F)
  proof +-invˡ   ρ = +-invˡ-≡   (ρ 0F)
  proof +-invʳ   ρ = +-invʳ-≡   (ρ 0F)
  proof +-comm   ρ = +-comm-≡   (ρ 0F) (ρ 1F)
  proof ·-assoc  ρ = *-assoc-≡  (ρ 0F) (ρ 1F) (ρ 2F)
  proof ·-idˡ    ρ = *-idˡ-≡    (ρ 0F)
  proof ·-idʳ    ρ = *-idʳ-≡    (ρ 0F)
  proof distribˡ ρ = distribˡ-≡ (ρ 0F) (ρ 1F) (ρ 2F)
  proof distribʳ ρ = distribʳ-≡ (ρ 0F) (ρ 1F) (ρ 2F)
```
