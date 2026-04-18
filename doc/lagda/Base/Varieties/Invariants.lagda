---
layout: default
title : "Base.Varieties.Invariants module (Agda Universal Algebra Library)"
date : "2021-06-29"
author: "the ualib/agda-algebras development team"
---

### Algebraic invariants

These are properties that are preserved under isomorphism.

\begin{code}

{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Base.Varieties.Invariants (𝑆 : Signature 𝓞 𝓥) where

-- Imports from Agda and the Agda Standard Library ---------------------
open import Agda.Primitive  using () renaming ( Set to Type )
open import Level           using ( Level )
open import Relation.Unary  using ( Pred )

-- Imports from the Agda Universal Algebra Library -------------------------------------------
open import Base.Homomorphisms   {𝑆 = 𝑆} using ( _≅_ )
open import Base.Algebras.Basic  {𝑆 = 𝑆} using ( Algebra )

private variable α ℓ : Level

AlgebraicInvariant : Pred (Algebra α) ℓ → Type _
AlgebraicInvariant P = ∀ 𝑨 𝑩 → P 𝑨 → 𝑨 ≅ 𝑩 → P 𝑩

\end{code}

--------------------------------

{% include UALib.Links.md %}
