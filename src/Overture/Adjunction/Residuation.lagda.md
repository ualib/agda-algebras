---
layout: default
title : "Overture.Adjunction.Residuation module (The Agda Universal Algebra Library)"
date : "2026-05-09"
author: "the agda-algebras development team"
---

### Residuation

This is the [Overture.Adjunction.Residuation][] module of the [Agda Universal Algebra Library][].

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Overture.Adjunction.Residuation where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library --------------------------------------
open import Function.Base            using ( _∘_ )
open import Level                    using ( Level ; _⊔_ ; suc )
open import Relation.Binary          using ( _Preserves_⟶_ ) renaming ( Rel to BinaryRel )
open import Relation.Binary.Bundles  using ( Poset )

-- Imports from agda-algebras -----------------------------------------------------------
open import Overture.Relations using ( PointWise )

private variable
 a ιᵃ α b ιᵇ β : Level
```
-->

```agda
module _ (𝑨 : Poset a ιᵃ α)(𝑩 : Poset b ιᵇ β) where
  open Poset 𝑨 renaming ( Carrier to A ; _≤_ to _≤ᴬ_ ) using ()
  open Poset 𝑩 renaming ( Carrier to B ; _≤_ to _≤ᴮ_ ) using ()

  record Residuation : Type (suc (α ⊔ a ⊔ β ⊔ b))  where
    field
      f      : A → B
      g      : B → A
      fhom   : f Preserves _≤ᴬ_ ⟶ _≤ᴮ_
      ghom   : g Preserves _≤ᴮ_ ⟶ _≤ᴬ_
      gf≥id  : ∀ a → a ≤ᴬ g (f a)
      fg≤id  : ∀ b → f (g b) ≤ᴮ b
```

#### Basic properties of residual pairs

```agda
-- open Residuation
-- open Poset

module _ {𝑨 : Poset a ιᵃ α} {𝑩 : Poset b ιᵇ β} (R : Residuation 𝑨 𝑩) where
  open Poset 𝑨 renaming ( Carrier to A ; _≤_ to _≤ᴬ_ ; _≈_ to _≈ᴬ_; antisym to antisymᴬ) using ()
  open Poset 𝑩 renaming ( Carrier to B ; _≤_ to _≤ᴮ_ ; _≈_ to _≈ᴮ_; antisym to antisymᴮ) using ()
  open Residuation R

  -- Pointwise equality of unary functions wrt equality on the given poset carrier
  -- 1. pointwise equality on B → A
  _≈A_ : BinaryRel (B → A) (ιᵃ ⊔ b)
  _≈A_ = PointWise{a = b}{A = B} (_≈ᴬ_)

  -- 2. pointwise equality on A → B
  _≈B_ : BinaryRel (A → B) (a ⊔ ιᵇ)
  _≈B_ = PointWise{a = a}{A = A} (_≈ᴮ_)
```


In a ring `R`, if `x y : R` and if `x y x = x`, then `y` is called a *weak inverse* for `x`.  (A ring is called *von Neumann regular* if every element has a unique weak inverse.)


```agda
  -- g is a weak inverse for f
  weak-inverse : (f ∘ g ∘ f) ≈B f
  weak-inverse a = antisymᴮ lt gt
    where
    lt : f (g (f a)) ≤ᴮ f a
    lt = fg≤id (f a)
    gt : f a ≤ᴮ f (g (f a))
    gt = fhom (gf≥id a)

 -- f is a weak inverse of g
  weak-inverse' : (g ∘ f ∘ g) ≈A g
  weak-inverse' b = antisymᴬ lt gt
    where
    lt : g (f (g b)) ≤ᴬ g b
    lt = ghom (fg≤id b)
    gt : g b ≤ᴬ g (f (g b))
    gt = gf≥id (g b)
```
