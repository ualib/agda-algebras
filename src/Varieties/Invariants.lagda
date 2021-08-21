---
layout: default
title : Varieties.Invariants module (Agda Universal Algebra Library)
date : 2021-06-29
author: [the ualib/agda-algebras development team][]
---

### Algebraic invariants

These are properties that are preserved under isomorphism.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature ; Algebra )

module Varieties.Invariants (𝑆 : Signature 𝓞 𝓥) where


-- Imports from Agda and the Agda Standard Library ---------------------
open import Agda.Primitive using ( Level ) renaming ( Set to Type )
open import Relation.Unary using ( Pred )

-- Imports from the Agda Universal Algebra Library -------------------------------------------
open import Homomorphisms.Isomorphisms {𝑆 = 𝑆} using ( _≅_ )

private variable α ℓ : Level
AlgebraicInvariant : Pred (Algebra α 𝑆) ℓ → Type _
AlgebraicInvariant P = ∀ 𝑨 𝑩 → P 𝑨 → 𝑨 ≅ 𝑩 → P 𝑩

\end{code}
