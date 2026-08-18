---
layout: default
file: "src/Classical/Structures/Group/Diagonal.lagda.md"
title: "Classical.Structures.Group.Diagonal module"
date: "2026-07-27"
author: "the agda-algebras development team"
---

### The diagonal subgroup of a power

This is the [Classical.Structures.Group.Diagonal][] module of the [Agda Universal Algebra Library][].

For a power `𝒢 ^ I` built by [Classical.Structures.Group.Power][], the
**diagonal** is the set of constant tuples,

    D = { (g, g, …, g) | g ∈ G } ≤ Gᴵ,

the image of the constant embedding `κ`{.AgdaFunction}` : G → Gᴵ`.  Over a setoid
carrier "constant" means *`≈`-constant*, so the predicate is stated as equality of
any two coordinate values: `Diag x = ∀ i j → x i ≈ x j`.  This form respects the
pointwise equality of the power by construction and needs no distinguished index,
so it is the canonical membership predicate; the pointed characterizations —
membership from and to an explicit constant value — are provided as lemmas for the
consumers that do fix an index (`Fin (suc m)`, say).

The diagonal is an equality-respecting subgroup (`IsSubgroup`{.AgdaRecord}): each
closure proof rewrites one coordinate of the curried power operation to the base
group by the pointwise descriptions of [Classical.Structures.Group.Power][], applies
the hypothesis coordinatewise, and folds back.[^1]

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.Diagonal where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Patterns            using ( 0F ; 1F )
open import Data.Product                 using ( Σ-syntax ; _,_ ; proj₁ )
open import Level                        using ( Level ; _⊔_ )
open import Relation.Binary              using ( Setoid )
open import Relation.Binary.Definitions  using ( _Respects_ )
open import Relation.Unary               using ( Pred ; _∈_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Signatures.Group            using ( ∙-Op ; ⁻¹-Op )
open import Classical.Structures.Group.Basic      using ( Group ; module Group-Op )
open import Classical.Structures.Group.Power      using ( module GroupPower )
open import Classical.Structures.Group.Subgroups  using ( IsSubgroup ; mkIsSubgroup )
open import Classical.Structures.Interpret        using ( interp-cong )
open import Setoid.Algebras.Basic                 using ( 𝕌[_] ; 𝔻[_] )

private variable ι α ρ : Level
```
-->

#### The diagonal predicate

`DiagonalSubgroup`{.AgdaModule}` I 𝒢` packages the diagonal of the power `𝒢 ^ I` for
a fixed index type and base group.

```agda
module DiagonalSubgroup (I : Type ι) (𝒢 : Group α ρ) where

  open GroupPower I 𝒢

  private
    𝑮 = 𝒢 .proj₁
    𝑮ᴵ = ⨅ᵍ-Group .proj₁

  open Setoid 𝔻[ 𝑮 ]  renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
                       using ( _≈_ )
  open Setoid 𝔻[ 𝑮ᴵ ]  renaming ( _≈_ to _≈ᴵ_ ) using ()

  -- Membership: all coordinate values agree.
  Diag : Pred 𝕌[ 𝑮ᴵ ] (ι ⊔ ρ)
  Diag x = ∀ i j → x i ≈ x j
```

The constant embedding, and the pointed characterizations of membership: a tuple
is diagonal exactly when it is `≈`-equal to a constant tuple, and any coordinate
supplies the constant.

```agda
  -- The constant embedding G → Gᴵ.
  κ : 𝕌[ 𝑮 ] → 𝕌[ 𝑮ᴵ ]
  κ g _ = g

  -- Constant tuples are diagonal.
  κ-diag : (g : 𝕌[ 𝑮 ]) → κ g ∈ Diag
  κ-diag g i j = ≈refl

  -- A tuple pointwise equal to a constant is diagonal.
  diag-from-const : {x : 𝕌[ 𝑮ᴵ ]} → Σ[ g ∈ 𝕌[ 𝑮 ] ] (∀ i → x i ≈ g) → x ∈ Diag
  diag-from-const (g , e) i j = ≈trans (e i) (≈sym (e j))

  -- Conversely, any coordinate value of a diagonal tuple is such a constant.
  diag-to-const : (i₀ : I) {x : 𝕌[ 𝑮ᴵ ]} → x ∈ Diag → Σ[ g ∈ 𝕌[ 𝑮 ] ] (∀ i → x i ≈ g)
  diag-to-const i₀ {x} d = x i₀ , λ i → d i i₀
```

#### The diagonal is a respecting subgroup

Each closure proof moves between the power operation and the base operations by
the pointwise descriptions, and applies the membership hypothesis coordinatewise.

```agda
  -- Diag respects the pointwise equality of the power.
  Diag-respects : Diag Respects _≈ᴵ_
  Diag-respects e d i j = ≈trans (≈sym (e i)) (≈trans (d i j) (e j))

  -- Diag is closed under the power operations, hence a respecting subgroup.
  Diag-isSubgroup : IsSubgroup ⨅ᵍ-Group Diag
  Diag-isSubgroup = mkIsSubgroup ⨅ᵍ-Group Diag-respects ∙-closed ε-closed ⁻¹-closed
    where
    open Group-Op ⨅ᵍ-Group  using () renaming ( _∙_ to _⊗_ ; ε to e ; _⁻¹ to inv )

    ∙-closed : ∀ {x y} → x ∈ Diag → y ∈ Diag → (x ⊗ y) ∈ Diag
    ∙-closed {x} {y} dx dy i j =
      ≈trans  (⊗-pointwise x y i)
              (≈trans  (interp-cong 𝑮 ∙-Op λ { 0F → dx i j ; 1F → dy i j })
                       (≈sym (⊗-pointwise x y j)))

    ε-closed : e ∈ Diag
    ε-closed i j = ≈trans (e-pointwise i) (≈sym (e-pointwise j))

    ⁻¹-closed : ∀ {x} → x ∈ Diag → (inv x) ∈ Diag
    ⁻¹-closed {x} d i j = ≈trans  (inv-pointwise x i)
                                  (≈trans  (interp-cong 𝑮 ⁻¹-Op λ { 0F → d i j })
                                           (≈sym (inv-pointwise x j)))
```
---

[^1]: The diagonal is the bottom of the interval `[D , Gⁿ]` that Kurzweil's construction
      inhabits (Issue #521); it is the bottom of the lattice of *partition subgroups*
      (the subject of [Classical.Structures.Group.PartitionSubgroup][]).
