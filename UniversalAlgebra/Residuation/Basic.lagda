---
layout: default
title : Residuation.Basic module (The Agda Universal Algebra Library)
date : 2021-07-12
author: [agda-algebras development team][]
---

## Residuation

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Residuation.Basic where

open import Agda.Primitive          using    ( _⊔_ ;  Level ; lsuc)
                                    renaming ( Set to Type )
open import Function.Base           using    ( _on_ )
open import Relation.Binary.Bundles using    ( Poset )
open import Relation.Binary.Core    using    ( _Preserves_⟶_ )


module _ {α ιᵃ ρᵃ : Level} (A : Poset α ιᵃ ρᵃ)
         {β ιᵇ ρᵇ : Level} (B : Poset β ιᵇ ρᵇ)
         where

 open Poset

 private
  _≤A_ = _≤_ A
  _≤B_ = _≤_ B

 record Residuation : Type (lsuc (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ))  where
  field
   f     : Carrier A → Carrier B
   g     : Carrier B → Carrier A
   fhom  : f Preserves _≤A_ ⟶ _≤B_
   ghom  : g Preserves _≤B_ ⟶ _≤A_
   gf≥id : ∀ a → a ≤A g (f a)
   fg≤id : ∀ b → f (g b) ≤B b


\end{code}
