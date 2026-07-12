---
layout: default
file: "src/Classical/Structures/Group/Cosets.lagda.md"
title: "Classical.Structures.Group.Cosets module"
date: "2026-07-11"
author: "the agda-algebras development team"
---

### Cosets and the coset space `G/H`

This is the [Classical.Structures.Group.Cosets][] module of the [Agda Universal Algebra Library][].

For a subgroup `H` of a group `𝑮`, two elements lie in the same **left coset**
exactly when `x ⁻¹ ∙ y ∈ H`.  In the setoid discipline the coset space `G/H` is not
a new carrier of equivalence classes but the *same* carrier with a coarser setoid
equality: the relation `_∼_` just described.

This module proves `_∼_` is an equivalence relation — each axiom is one subgroup
closure property plus one line of group arithmetic — and packages the quotient setoid
`cosetSetoid`{.AgdaFunction} via the `_/_`{.AgdaFunction} construction of
[Setoid.Relations.Quotients][].

Two further lemmas prepare the ground for the coset action of
[Classical.Structures.Group.GSet][]: the original setoid equality refines the coset
equality (`≈⇒∼`{.AgdaFunction}, well-definedness of the quotient map), and left
translation by any group element preserves the coset equality
(`∼-congˡ`{.AgdaFunction}, which will be the congruence proof of the action).

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.Cosets where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Product    using ( _,_ ; proj₁ ; proj₂ )
open import Level           using ( Level )
open import Relation.Binary using ( Setoid ; IsEquivalence )
open import Relation.Unary  using ( Pred ; _∈_ )

import Algebra.Properties.Group as GroupProperties
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Overture                               using ( Equivalence )
open import Classical.Bundles.Group                using ( ⟨_⟩ᵍᵖ )
open import Classical.Signatures.Group             using ( Sig-Group )
open import Classical.Structures.Group.Basic       using ( Group ; module Group-Op )
open import Classical.Structures.Group.Subgroups   using ( IsSubgroup )
open import Setoid.Relations.Quotients             using ( _/_ )

open import Setoid.Algebras.Basic {𝑆 = Sig-Group}  using ( Algebra ; 𝕌[_] ; 𝔻[_] )
```
-->

#### The coset relation

```agda
module Coset {α ρ : Level} (𝒢 : Group α ρ) {ℓ : Level}
  (H : Pred 𝕌[ proj₁ 𝒢 ] ℓ) (H-isSubgroup : IsSubgroup 𝒢 H)
  where

  private
    𝑮 = proj₁ 𝒢
    G = 𝕌[ 𝑮 ]

  open Setoid 𝔻[ 𝑮 ]            using ( _≈_ )
                                renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open SetoidReasoning 𝔻[ 𝑮 ]
  open Group-Op 𝒢               using  ( _∙_ ; ε ; _⁻¹ ; ∙-cong ; ⁻¹-cong
                                       ; assoc-law ; invˡ-law )
  open GroupProperties ⟨ 𝒢 ⟩ᵍᵖ  using  ( ⁻¹-involutive ; ⁻¹-anti-homo-∙
                                       ; \\-leftDividesˡ ; \\-leftDividesʳ )
  open IsSubgroup H-isSubgroup  using  ( respects ; ∙-closed ; ε-closed ; ⁻¹-closed )

  infix 4 _∼_

  -- x and y lie in the same left coset of H when x ⁻¹ ∙ y ∈ H.
  _∼_ : G → G → Type ℓ
  x ∼ y = x ⁻¹ ∙ y ∈ H
```

#### `_∼_` is an equivalence relation

Reflexivity is `ε ∈ H` transported along `x ⁻¹ ∙ x ≈ ε`; symmetry is closure of `H`
under inverses, since `(x ⁻¹ ∙ y) ⁻¹ ≈ y ⁻¹ ∙ x`; and transitivity is closure under
products, since `(x ⁻¹ ∙ y) ∙ (y ⁻¹ ∙ z) ≈ x ⁻¹ ∙ z`.

```agda
  ∼-refl : ∀ {x} → x ∼ x
  ∼-refl {x} = respects (≈sym (invˡ-law x)) ε-closed

  ∼-sym : ∀ {x y} → x ∼ y → y ∼ x
  ∼-sym {x} {y} x∼y = respects inv-eq (⁻¹-closed x∼y)
    where
    inv-eq : (x ⁻¹ ∙ y) ⁻¹ ≈ y ⁻¹ ∙ x
    inv-eq = begin
      (x ⁻¹ ∙ y) ⁻¹     ≈⟨ ⁻¹-anti-homo-∙ (x ⁻¹) y ⟩
      y ⁻¹ ∙ (x ⁻¹) ⁻¹  ≈⟨ ∙-cong ≈refl (⁻¹-involutive x) ⟩
      y ⁻¹ ∙ x          ∎

  ∼-trans : ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z
  ∼-trans {x} {y} {z} x∼y y∼z = respects prod-eq (∙-closed x∼y y∼z)
    where
    prod-eq : (x ⁻¹ ∙ y) ∙ (y ⁻¹ ∙ z) ≈ x ⁻¹ ∙ z
    prod-eq = begin
      (x ⁻¹ ∙ y) ∙ (y ⁻¹ ∙ z)  ≈⟨ assoc-law (x ⁻¹) y (y ⁻¹ ∙ z) ⟩
      x ⁻¹ ∙ (y ∙ (y ⁻¹ ∙ z))  ≈⟨ ∙-cong ≈refl (\\-leftDividesˡ y z) ⟩
      x ⁻¹ ∙ z                 ∎

  ∼-isEquivalence : IsEquivalence _∼_
  ∼-isEquivalence = record { refl = ∼-refl ; sym = ∼-sym ; trans = ∼-trans }

  ∼-equivalence : Equivalence G {ℓ}
  ∼-equivalence = _∼_ , ∼-isEquivalence
```

#### Compatibility lemmas

```agda
  -- The setoid equality refines the coset equality (the quotient map is well defined).
  ≈⇒∼ : ∀ {x y} → x ≈ y → x ∼ y
  ≈⇒∼ {x} {y} x≈y = respects (≈sym unit-eq) ε-closed
    where
    unit-eq : x ⁻¹ ∙ y ≈ ε
    unit-eq = ≈trans (∙-cong (⁻¹-cong x≈y) ≈refl) (invˡ-law y)

  -- Left translation by any group element preserves the coset equality.
  ∼-congˡ : ∀ g {x y} → x ∼ y → (g ∙ x) ∼ (g ∙ y)
  ∼-congˡ g {x} {y} x∼y = respects (≈sym transl-eq) x∼y
    where
    transl-eq : (g ∙ x) ⁻¹ ∙ (g ∙ y) ≈ x ⁻¹ ∙ y
    transl-eq = begin
      (g ∙ x) ⁻¹ ∙ (g ∙ y)     ≈⟨ ∙-cong (⁻¹-anti-homo-∙ g x) ≈refl ⟩
      x ⁻¹ ∙ g ⁻¹ ∙ (g ∙ y)    ≈⟨ assoc-law (x ⁻¹) (g ⁻¹) (g ∙ y) ⟩
      x ⁻¹ ∙ (g ⁻¹ ∙ (g ∙ y))  ≈⟨ ∙-cong ≈refl (\\-leftDividesʳ g y) ⟩
      x ⁻¹ ∙ y                 ∎
```

#### The quotient setoid `G/H`

The coset space is the carrier of `𝒢` under the coset equality, assembled by the
quotient construction of [Setoid.Relations.Quotients][].

```agda
  cosetSetoid : Setoid α ℓ
  cosetSetoid = G / ∼-equivalence
```
