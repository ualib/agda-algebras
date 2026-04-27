---
layout: default
title : "Base.Adjunction.Residuation module (The Agda Universal Algebra Library)"
date : "2021-07-12"
author: "agda-algebras development team"
---

### <a id="residuation">Residuation</a>

This is the [Base.Adjunction.Residuation][] module of the [Agda Universal Algebra Library][].


```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Base.Adjunction.Residuation where

-- Imports from Agda and the Agda Standard Library --------------------------------------
open import Agda.Primitive           using () renaming ( Set to Type )
open import Function.Base            using ( _on_ ; _∘_ )
open import Level                    using ( Level ; _⊔_ ; suc )
open import Relation.Binary.Bundles  using ( Poset )
open import Relation.Binary.Core     using ( _Preserves_⟶_ )

-- Imports from the Agda Universal Algebra Library --------------------------------------
open import Base.Relations.Discrete using ( PointWise )

private variable
 a ιᵃ α b ιᵇ β : Level

module _ (A : Poset a ιᵃ α)(B : Poset b ιᵇ β) where
 open Poset
 private
  _≤A_ = _≤_ A
  _≤B_ = _≤_ B

 record Residuation : Type (suc (α ⊔ a ⊔ β ⊔ b))  where
  field
   f      : Carrier A → Carrier B
   g      : Carrier B → Carrier A
   fhom   : f Preserves _≤A_ ⟶ _≤B_
   ghom   : g Preserves _≤B_ ⟶ _≤A_
   gf≥id  : ∀ a → a ≤A g (f a)
   fg≤id  : ∀ b → f (g b) ≤B b
```



#### <a id="basic-properties-of-residual-pairs">Basic properties of residual pairs</a>


```agda


open Residuation
open Poset

module _ {A : Poset a ιᵃ α} {B : Poset b ιᵇ β} (R : Residuation A B) where
 private
  _≤A_ = _≤_ A
  _≤B_ = _≤_ B

  𝑓 = (R .f)
  𝑔 = (R .g)

  -- Pointwise equality of unary functions wrt equality on the given poset carrier
  -- 1. pointwise equality on B → A
  _≈̇A_ = PointWise{a = b}{A = Carrier B} (_≈_ A)
  -- 2. pointwise equality on A → B
  _≈̇B_ = PointWise{a = a}{A = Carrier A} (_≈_ B)
```


In a ring `R`, if `x y : R` and if `x y x = x`, then `y` is called a *weak inverse* for `x`.
(A ring is called *von Neumann regular* if every element has a unique weak inverse.) 


```agda


 -- 𝑔 is a weak inverse for 𝑓
 weak-inverse : (𝑓 ∘ 𝑔 ∘ 𝑓) ≈̇B 𝑓
 weak-inverse a = antisym B lt gt
  where
  lt : 𝑓 (𝑔 (𝑓 a)) ≤B 𝑓 a
  lt = fg≤id R (𝑓 a)
  gt : 𝑓 a ≤B 𝑓 (𝑔 (𝑓 a))
  gt = fhom R (gf≥id R a)

 -- 𝑓 is a weak inverse of 𝑔
 weak-inverse' : (𝑔 ∘ 𝑓 ∘ 𝑔) ≈̇A 𝑔
 weak-inverse' b = antisym A lt gt
  where
  lt : 𝑔 (𝑓 (𝑔 b)) ≤A 𝑔 b
  lt = ghom R (fg≤id R b)
  gt : 𝑔 b ≤A 𝑔 (𝑓 (𝑔 b))
  gt = gf≥id R (𝑔 b)
```


------------------------------------------

<span style="float:left;">[← Base.Adjunction.Galois ](Base.Adjunction.Galois.html)</span>
<span style="float:right;">[Base.Categories →](Base.Categories.html)</span>

{% include UALib.Links.md %}
