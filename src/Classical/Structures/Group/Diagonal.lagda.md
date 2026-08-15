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

$$D \;=\; \{\, (s, s, \dots, s) \mid s \in S \,\} \;\leq\; S^I ,$$

the image of the constant embedding `κ`{.AgdaFunction}` : S → Sᴵ`.  Over a setoid
carrier "constant" means *`≈`-constant*, so the predicate is stated as equality of
any two coordinate values: `Diag x = ∀ i j → x i ≈ x j`.  This form respects the
pointwise equality of the power by construction and needs no distinguished index,
so it is the canonical membership predicate; the pointed characterizations —
membership from and to an explicit constant value — are provided as lemmas for the
consumers that do fix an index (`Fin (suc m)`, say).

The diagonal is an equality-respecting subgroup (`IsSubgroup`{.AgdaRecord}): each
closure proof rewrites one coordinate of the curried power operation to the base
group by the pointwise descriptions of [Classical.Structures.Group.Power][], applies
the hypothesis coordinatewise, and folds back.

The diagonal is the bottom of the interval `[D , Sⁿ]` that Kurzweil's construction
inhabits (issue #521); the partition subgroups whose least member it is are the
subject of [Classical.Structures.Group.PartitionSubgroup][].

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.Diagonal where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Patterns   using ( 0F ; 1F )
open import Data.Product        using ( Σ-syntax ; _,_ ; proj₁ ; proj₂ )
open import Level               using ( Level ; _⊔_ )
open import Relation.Binary     using ( Setoid )
open import Relation.Binary.Definitions   using ( _Respects_ )
open import Relation.Unary      using ( Pred ; _∈_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Signatures.Group          using  ( Sig-Group ; ∙-Op ; ε-Op
                                                       ; ⁻¹-Op )
open import Classical.Structures.Group.Basic    using  ( Group ; module Group-Op )
open import Classical.Structures.Group.Power    using  ( module GroupPower )
open import Classical.Structures.Group.Subgroups
                                                using  ( IsSubgroup ; mkIsSubgroup )
open import Classical.Structures.Interpret      using  ( interp-cong )
open import Setoid.Algebras.Basic               using  ( 𝕌[_] ; 𝔻[_] )

private variable ι α ρ : Level
```
-->

#### The diagonal predicate

`DiagonalSubgroup`{.AgdaModule} `I` `𝒢` packages the diagonal of the power
`𝒢 ^ I` for a fixed index type and base group.

```agda
module DiagonalSubgroup (I : Type ι) (𝒢 : Group α ρ) where

  open GroupPower I 𝒢

  private
    𝑮 = proj₁ 𝒢
    𝑷 = proj₁ ⨅ᵍ-Group

  open Setoid 𝔻[ 𝑮 ] using ()
    renaming ( _≈_ to _≈₁_ ; refl to refl₁ ; sym to sym₁ ; trans to trans₁ )
  open Setoid 𝔻[ 𝑷 ] using () renaming ( _≈_ to _≈ₚ_ )

  -- Membership: all coordinate values agree.
  Diag : Pred 𝕌[ 𝑷 ] (ι ⊔ ρ)
  Diag x = ∀ i j → x i ≈₁ x j
```

The constant embedding, and the pointed characterizations of membership: a tuple
is diagonal exactly when it is `≈`-equal to a constant tuple, and any coordinate
supplies the constant.

```agda
  -- The constant embedding S → Sᴵ.
  κ : 𝕌[ 𝑮 ] → 𝕌[ 𝑷 ]
  κ s _ = s

  -- Constant tuples are diagonal.
  κ-diag : (s : 𝕌[ 𝑮 ]) → κ s ∈ Diag
  κ-diag s i j = refl₁

  -- A tuple pointwise equal to a constant is diagonal.
  diag-from-const : {x : 𝕌[ 𝑷 ]} → Σ[ s ∈ 𝕌[ 𝑮 ] ] (∀ i → x i ≈₁ s) → x ∈ Diag
  diag-from-const (s , e) i j = trans₁ (e i) (sym₁ (e j))

  -- Conversely, any coordinate value of a diagonal tuple is such a constant.
  diag-to-const : (i₀ : I) {x : 𝕌[ 𝑷 ]} → x ∈ Diag → Σ[ s ∈ 𝕌[ 𝑮 ] ] (∀ i → x i ≈₁ s)
  diag-to-const i₀ {x} d = x i₀ , λ i → d i i₀
```

#### The diagonal is a respecting subgroup

Each closure proof moves between the power operation and the base operations by
the pointwise descriptions, and applies the membership hypothesis coordinatewise.

```agda
  -- Diag respects the pointwise equality of the power.
  Diag-respects : Diag Respects _≈ₚ_
  Diag-respects e d i j = trans₁ (sym₁ (e i)) (trans₁ (d i j) (e j))

  -- Diag is closed under the power operations, hence a respecting subgroup.
  Diag-isSubgroup : IsSubgroup ⨅ᵍ-Group Diag
  Diag-isSubgroup = mkIsSubgroup ⨅ᵍ-Group Diag-respects ∙-closed ε-closed ⁻¹-closed
    where
    open Group-Op 𝒢         using () renaming ( _∙_ to _∙₁_ ; ε to ε₁ ; _⁻¹ to _⁻¹₁ )
    open Group-Op ⨅ᵍ-Group  using () renaming ( _∙_ to _∙ₚ_ ; ε to εₚ ; _⁻¹ to _⁻¹ₚ )

    ∙-closed : ∀ {x y} → x ∈ Diag → y ∈ Diag → (x ∙ₚ y) ∈ Diag
    ∙-closed {x} {y} dx dy i j =
      trans₁  (∙ₚ-pointwise x y i)
              (trans₁  (interp-cong 𝑮 ∙-Op (λ { 0F → dx i j ; 1F → dy i j }))
                       (sym₁ (∙ₚ-pointwise x y j)))

    ε-closed : εₚ ∈ Diag
    ε-closed i j = trans₁ (εₚ-pointwise i) (sym₁ (εₚ-pointwise j))

    ⁻¹-closed : ∀ {x} → x ∈ Diag → (x ⁻¹ₚ) ∈ Diag
    ⁻¹-closed {x} d i j =
      trans₁  (⁻¹ₚ-pointwise x i)
              (trans₁  (interp-cong 𝑮 ⁻¹-Op (λ { 0F → d i j }))
                       (sym₁ (⁻¹ₚ-pointwise x j)))
```
