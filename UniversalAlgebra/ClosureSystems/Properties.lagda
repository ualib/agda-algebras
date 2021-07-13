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

open import Agda.Primitive              using    ( _⊔_   ;  Level  )
                                        renaming ( Set   to Type   )
open import Data.Product                using    ( _,_   ;   _×_   )
                                        renaming ( proj₁ to  fst
                                                 ; proj₂ to  snd   )
open import Function.Bundles            using    ( _↔_   ; Inverse )
open import Relation.Binary.Bundles     using    ( Poset           )
open import Relation.Binary.Definitions using    ( Reflexive ; Transitive ; Antisymmetric )
open import Relation.Binary.Structures  using    ( IsPreorder ; IsPartialOrder     )
import      Relation.Binary.Reasoning.PartialOrder as ≤-Reasoning

open import ClosureSystems.Basic        using    ( ClOp            )
open import ClosureSystems.Definitions  using    ( Extensive
                                                 ; OrderPreserving
                                                 ; Idempotent      )
open ClOp
open Inverse


module _ {ℓ ℓ₁ ℓ₂ : Level}{𝑨 : Poset ℓ ℓ₁ ℓ₂}(𝑪 : ClOp 𝑨) where
 open Poset 𝑨
 open ≤-Reasoning 𝑨

 private
  c = C 𝑪
  A = Carrier

 -- Theorem 1. If `𝑨 = (A , ≦)` is a poset and `c` is a closure operator on A, then
 --            ∀ (x y : A) → (x ≦ (c y) ↔ (c x) ≦ (c y))
 --
 clop→law⇒ : (x y : A) → x ≤ (c y) → (c x) ≤ (c y)
 clop→law⇒ x y x≤cy = begin
   c x     ≤⟨ isOrderPreserving 𝑪 x≤cy ⟩
   c (c y) ≈⟨ isIdempotent 𝑪 ⟩
   c y ∎

 clop→law⇐ : (x y : A) → (c x) ≤ (c y) → x ≤ (c y)
 clop→law⇐ x y cx≤cy = begin
   x   ≤⟨ isExtensive 𝑪 ⟩
   c x ≤⟨ cx≤cy ⟩
   c y ∎

module _ {ℓ ℓ₁ ℓ₂ : Level}{𝑨 : Poset ℓ ℓ₁ ℓ₂} where
 open Poset 𝑨

 private
  A = Carrier

 -- The converse of Theorem 1 also holds.
 --
 -- Theorem 2. If `𝑨 = (A , ≤)` is a poset and `c : A → A` satisfies
 --            ∀ (x y : A) → (x ≤ (c y) ↔ (c x) ≤ (c y))
 --            then `c` is a closure operator on A.
 --
 clop←law : (c : A → A) → ((x y : A) → (x ≤ (c y) ↔ (c x) ≤ (c y)))
  →         Extensive _≤_ c × OrderPreserving _≤_ c × Idempotent _≈_ c

 clop←law c hyp  = e , (o , i)
  where
  h1 : ∀ {x y} → x ≤ (c y) → c x ≤ c y
  h1 {x}{y} = f (hyp x y)

  h2 : ∀ {x y} → c x ≤ c y → x ≤ (c y)
  h2 {x}{y} = f⁻¹ (hyp x y)

  η : ∀ {x} →  c (c x) ≤ c x
  η = h1 refl

  η' : ∀ {x} → c x ≤ c (c x)
  η' = h2 refl

  e : Extensive _≤_ c
  e = h2 refl

  o : OrderPreserving _≤_ c
  o u = h1 (trans u e)

  i : Idempotent _≈_ c
  i = antisym η η'

\end{code}




--------------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
