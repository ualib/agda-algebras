---
layout: default
title : GaloisConnections.Basic module (The Agda Universal Algebra Library)
date : 2021-07-01
author: [the agda-algebras development team][]
---

## Galois Connection

If 𝑨 = (A, ≤) and 𝑩 = (B, ≤) are two partially ordered sets (posets), then a
*Galois connection* between 𝑨 and 𝑩 is a pair (F , G) of functions such that

1. F : A → B
2. G : B → A
3. ∀ (a : A)(b : B)  →  F(a) ≤   b   →    a  ≤ G(b)
r. ∀ (a : A)(b : B)  →    a  ≤ G(b)  →  F(a) ≤   b

In other terms, F is a left adjoint of G and G is a right adjoint of F.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module GaloisConnections.Basic where

open import Agda.Primitive          using    ( _⊔_ ;  Level )
                                    renaming ( Set to Type  )
open import Relation.Binary.Bundles using    ( Poset        )

module _ {α α₁ α₂ : Level}(A : Poset α α₁ α₂)
         {β β₁ β₂ : Level}(B : Poset β β₁ β₂)
         where

 open Poset

 private
  _≤A_ = _≤_ A
  _≤B_ = _≤_ B

 record Galois : Type  (α ⊔ α₂ ⊔ β ⊔ β₂) where
  field
   F : Carrier A → Carrier B
   G : Carrier B → Carrier A
   F⊣G : ∀ a b → (F a) ≤B b → a ≤A (G b)
   F⊢G : ∀ a b → a ≤A (G b) → (F a) ≤B b


\end{code}




--------------------------------------

[the agda-algebras development team]: https://github.com/ualib/agda-algebras#the-ualib-agda-algebras-development-team

