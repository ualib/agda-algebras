---
layout: default
title : Relations.GaloisConnections module (The Agda Universal Algebra Library)
date : 2021-07-01
author: [the ualib/agda-algebras development team][]
---

## Galois Connections

If 𝑨 = (A, ≤) and 𝑩 = (B, ≤) are two partially ordered sets (posets), then a
*Galois connection* between 𝑨 and 𝑩 is a pair (F , G) of functions such that

1. F : A → B
2. G : B → A
3. ∀ (a : A) (b : B)  →   (F(a) ≤ b  ↔  a ≤ G(b))

That is, F is a left adjoint of G and G is a right adjoint of F.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Relation.Binary.Bundles using (Poset)
open import Relation.Binary.Core
open import Agda.Primitive          using    ( _⊔_ ;  lsuc ; Level)
                                    renaming ( Set to Type )

module Relations.GaloisConnection
 {α α₁ α₂ : Level}(𝑨 : Poset α α₁ α₂)
 {β β₁ β₂ : Level}(𝑩 : Poset β β₁ β₂)
 where

open Poset

private
 A = Carrier 𝑨
 B = Carrier 𝑩
 _≤A_ = _≤_ 𝑨
 _≤B_ = _≤_ 𝑩

record GaloisConnex : Type  (α ⊔ α₂ ⊔ β ⊔ β₂) where
 field
  F : A → B
  G : B → A
  F⊣G : ∀ a b → (F a) ≤B b → a ≤A (G b)
  F⊢G : ∀ a b → a ≤A (G b) → (F a) ≤B b

\end{code}
