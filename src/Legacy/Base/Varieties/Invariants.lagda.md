---
layout: default
title : "Base.Varieties.Invariants module (Agda Universal Algebra Library)"
date : "2021-06-29"
author: "the ualib/agda-algebras development team"
---

### Algebraic invariants

These are properties that are preserved under isomorphism.


```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Legacy.Base.Varieties.Invariants (𝑆 : Signature 𝓞 𝓥) where

-- Imports from Agda and the Agda Standard Library ---------------------
open import Agda.Primitive  using () renaming ( Set to Type )
open import Level           using ( Level )
open import Relation.Unary  using ( Pred )

-- Imports from the Agda Universal Algebra Library -------------------------------------------
open import Legacy.Base.Homomorphisms   {𝑆 = 𝑆} using ( _≅_ )
open import Legacy.Base.Algebras.Basic  {𝑆 = 𝑆} using ( Algebra )

private variable α ℓ : Level

AlgebraicInvariant : Pred (Algebra α) ℓ → Type _
AlgebraicInvariant P = ∀ 𝑨 𝑩 → P 𝑨 → 𝑨 ≅ 𝑩 → P 𝑩
```


--------------------------------

{% include UALib.Links.md %}
