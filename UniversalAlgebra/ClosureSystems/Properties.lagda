---
layout: default
title : ClosureSystems.Properties module (The Agda Universal Algebra Library)
date : 2021-07-08
author: [agda-algebras development team][]
---

### Properties of Closure Systems and Operators


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module ClosureSystems.Properties where

open import Agda.Primitive              using    ( _⊔_ ;  Level    )
                                        renaming ( Set to Type     )
open import Data.Product                using    ( _,_ ;  _×_      )
open import Function.Bundles            using    ( _↔_             )
open import Relation.Binary.Bundles     using    ( Poset           )
open import Relation.Binary.Definitions using    ( Transitive      )
open import Relation.Binary.Structures  using    ( IsPreorder      )

open import ClosureSystems.Basic        using    ( ClOp            )
open import ClosureSystems.Definitions  using    ( Extensive
                                                 ; OrderPreserving
                                                 ; Idempotent      )
open Poset
open ClOp

module _ {ℓ ℓ₁ ℓ₂ : Level}{𝑨 : Poset ℓ ℓ₁ ℓ₂}{𝑪 : ClOp {ℓ}{ℓ₁}{ℓ₂} 𝑨} where

 private
  c = C 𝑪
  A = Carrier 𝑨
  _≦_ = _≤_ 𝑨
  _≋_ = _≈_ 𝑨

 -- Theorem 1. If `𝑨 = (A , ≦)` is a poset and `c` is a closure operator on A, then
 --            ∀ (x y : A) → (x ≦ (c y) ↔ (c x) ≦ (c y))
 --
 -- We prove the two directions separately as ClOpLemma1 and ClOpLemma2.

 ClOpLemma1 : (x y : A) → x ≦ (c y) → (c x) ≦ (c y)
 ClOpLemma1 x y x≦cy = IsPreorder.trans (isPreorder 𝑨) ξ η
  where
  ξ : c x ≦ c (c y)
  ξ = (isOrderPreserving 𝑪) x≦cy
  ζ : c (c y) ≋ c y
  ζ = isIdempotent 𝑪
  η : c (c y) ≦ c y
  η = reflexive 𝑨 ζ

 ClOpLemma2 : (x y : A) → (c x) ≦ (c y) → x ≦ (c y)
 ClOpLemma2 x y cx≦cy = ≦trans ζ cx≦cy
  where
  ζ : x ≦ c x
  ζ = isExtensive 𝑪
  ≦trans : Transitive _≦_
  ≦trans = IsPreorder.trans (isPreorder 𝑨)


module _ {ℓ ℓ₁ ℓ₂ : Level}{𝑨 : Poset ℓ ℓ₁ ℓ₂} where
 private
  A = Carrier 𝑨
  _≦_ = _≤_ 𝑨
  ≋ = _≈_ 𝑨

 -- The converse of Theorem 1 also holds.
 --
 -- Theorem 2. If `𝑨 = (A , ≦)` is a poset and `c : A → A` satisfies
 --            ∀ (x y : A) → (x ≦ (c y) ↔ (c x) ≦ (c y))
 --            then `c` is a closure operator on A.

 -- TODO: formalize the proof of Theorem 2 by proving the following.
 -- ClOpLemma3 : (c : A → A) → ((x y : A) → (x ≦ (c y) ↔ (c x) ≦ (c y)))
 --  →           Extensive _≦_ c × OrderPreserving _≦_ c × Idempotent ≋ c
 -- ClOpLemma3 c hyp  = {!!}

\end{code}




--------------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

