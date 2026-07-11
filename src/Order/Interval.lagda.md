---
layout: default
title : "Order.Interval module (The Agda Universal Algebra Library)"
date : "2026-07-11"
author: "agda-algebras development team"
---

### Intervals in lattices

This is the [Order.Interval][] module of the [Agda Universal Algebra Library][].

For elements `a ≤ b` of an (order-theoretic) lattice `L`, the **interval**
`[a, b] = { x ∣ a ≤ x ≤ b }` is again a lattice under the restricted order — meets
and joins of elements between the bounds stay between the bounds — and it is
*bounded*, with bottom `a` and top `b`.  This module packages that construction
generically over the standard library's `Relation.Binary.Lattice` bundles, as the
parameterized module `IntervalLattice`{.AgdaModule}.

The construction is pure order theory, so it lives in the top-level `Order/` tree
alongside [Order.CompleteLattice][].  The motivating instances are the *upper
intervals* `[H, G]` in subgroup lattices — apply `IntervalLattice`{.AgdaModule} to
the `Sub-Lattice`{.AgdaFunction} bundle of [Setoid.Subalgebras.CompleteLattice][]
(packaged for groups by [Classical.Structures.Group.SubgroupLattice][]) — which are
the central objects of the finite lattice representation problem: the Pálfy–Pudlák
correspondence identifies `Con (G ↷ G/H)` with exactly such an interval.

An interval element is a `Σ`-triple: an element of `L` together with the two bound
proofs.  The equality and order ignore the proof components (they compare first
components only), so no proof-irrelevance assumptions are needed.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Order.Interval where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Product                  using ( _,_ ; _×_ ; Σ-syntax ; proj₁ ; proj₂ )
open import Level                         using ( Level ; _⊔_ )
open import Relation.Binary               using ( IsEquivalence ; IsPartialOrder )
open import Relation.Binary.Definitions   using ( Maximum ; Minimum )
open import Relation.Binary.Lattice       using ( Supremum ; Infimum ; IsLattice ; Lattice
                                                ; IsBoundedLattice ; BoundedLattice )
```
-->

#### The interval as a bounded lattice

```agda
module IntervalLattice {c ℓ₁ ℓ₂ : Level} (L : Lattice c ℓ₁ ℓ₂)
  (a b : Lattice.Carrier L) (a≤b : Lattice._≤_ L a b)
  where

  open Lattice L
    using ( x≤x∨y ; y≤x∨y ; ∨-least ; x∧y≤x ; x∧y≤y ; ∧-greatest ; module Eq )
    renaming ( Carrier to X ; _≈_ to _≈ˣ_ ; _≤_ to _≤ˣ_ ; _∨_ to _∨ˣ_ ; _∧_ to _∧ˣ_
             ; refl to ≤ˣ-refl ; trans to ≤ˣ-trans ; antisym to ≤ˣ-antisym
             ; reflexive to ≤ˣ-reflexive )

  -- An element of the interval: an element of L with proofs of both bounds.
  Interval : Type (c ⊔ ℓ₂)
  Interval = Σ[ x ∈ X ] (a ≤ˣ x) × (x ≤ˣ b)

  infix 4 _≈_ _≤_

  -- Equality and order compare the underlying elements; bound proofs are ignored.
  _≈_ : Interval → Interval → Type ℓ₁
  x ≈ y = proj₁ x ≈ˣ proj₁ y

  _≤_ : Interval → Interval → Type ℓ₂
  x ≤ y = proj₁ x ≤ˣ proj₁ y

  infixr 6 _∨_
  infixr 7 _∧_

  -- Join and meet are those of L; both stay inside the interval.
  _∨_ : Interval → Interval → Interval
  (x , a≤x , x≤b) ∨ (y , a≤y , y≤b) =
    x ∨ˣ y , ≤ˣ-trans a≤x (x≤x∨y x y) , ∨-least x≤b y≤b

  _∧_ : Interval → Interval → Interval
  (x , a≤x , x≤b) ∧ (y , a≤y , y≤b) =
    x ∧ˣ y , ∧-greatest a≤x a≤y , ≤ˣ-trans (x∧y≤x x y) x≤b

  -- The order structure is inherited from L componentwise.
  ≈-isEquivalence : IsEquivalence _≈_
  ≈-isEquivalence = record { refl = Eq.refl ; sym = Eq.sym ; trans = Eq.trans }

  ≤-isPartialOrder : IsPartialOrder _≈_ _≤_
  ≤-isPartialOrder = record
    { isPreorder = record  { isEquivalence  = ≈-isEquivalence
                           ; reflexive      = ≤ˣ-reflexive
                           ; trans          = ≤ˣ-trans
                           }
    ; antisym = ≤ˣ-antisym
    }

  -- The join is the least upper bound and the meet the greatest lower bound,
  -- again componentwise from L.
  ∨-supremum : Supremum _≤_ _∨_
  ∨-supremum x y =  x≤x∨y (proj₁ x) (proj₁ y)
                 ,  y≤x∨y (proj₁ x) (proj₁ y)
                 ,  λ _ x≤z y≤z → ∨-least x≤z y≤z

  ∧-infimum : Infimum _≤_ _∧_
  ∧-infimum x y =  x∧y≤x (proj₁ x) (proj₁ y)
                ,  x∧y≤y (proj₁ x) (proj₁ y)
                ,  λ _ z≤x z≤y → ∧-greatest z≤x z≤y

  Interval-isLattice : IsLattice _≈_ _≤_ _∨_ _∧_
  Interval-isLattice = record  { isPartialOrder  = ≤-isPartialOrder
                               ; supremum        = ∨-supremum
                               ; infimum         = ∧-infimum
                               }

  Interval-Lattice : Lattice (c ⊔ ℓ₂) ℓ₁ ℓ₂
  Interval-Lattice = record  { Carrier    = Interval
                             ; _≈_        = _≈_
                             ; _≤_        = _≤_
                             ; _∨_        = _∨_
                             ; _∧_        = _∧_
                             ; isLattice  = Interval-isLattice
                             }
```

#### The bounds

The interval is a bounded lattice: `a` (with trivial bound proofs) is the least
element and `b` the greatest.

```agda
  0ᴵ : Interval
  0ᴵ = a , ≤ˣ-refl , a≤b

  1ᴵ : Interval
  1ᴵ = b , a≤b , ≤ˣ-refl

  0ᴵ-minimum : Minimum _≤_ 0ᴵ
  0ᴵ-minimum x = proj₁ (proj₂ x)

  1ᴵ-maximum : Maximum _≤_ 1ᴵ
  1ᴵ-maximum x = proj₂ (proj₂ x)

  Interval-isBoundedLattice : IsBoundedLattice _≈_ _≤_ _∨_ _∧_ 1ᴵ 0ᴵ
  Interval-isBoundedLattice = record  { isLattice  = Interval-isLattice
                                      ; maximum    = 1ᴵ-maximum
                                      ; minimum    = 0ᴵ-minimum
                                      }

  Interval-BoundedLattice : BoundedLattice (c ⊔ ℓ₂) ℓ₁ ℓ₂
  Interval-BoundedLattice = record  { Carrier           = Interval
                                    ; _≈_               = _≈_
                                    ; _≤_               = _≤_
                                    ; _∨_               = _∨_
                                    ; _∧_               = _∧_
                                    ; ⊤                 = 1ᴵ
                                    ; ⊥                 = 0ᴵ
                                    ; isBoundedLattice  = Interval-isBoundedLattice
                                    }
```
