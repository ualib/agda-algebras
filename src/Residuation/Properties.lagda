---
layout: default
title : Residuation.Properties module (The Agda Universal Algebra Library)
date : 2021-07-12
author: [agda-algebras development team][]
---

## Residuation Properties

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Residuation.Properties where

open import Agda.Primitive          using ( _⊔_ ; Level ; lsuc) renaming ( Set to Type )
open import Function.Base           using ( _on_ ; _∘_ )
open import Relation.Binary.Bundles using ( Poset )
open import Relation.Binary.Core    using ( _Preserves_⟶_ )

open import Relations.Discrete      using    ( PointWise )

open import Residuation.Basic
open Residuation
open Poset

module _ {α ιᵃ ρᵃ : Level} {A : Poset α ιᵃ ρᵃ}
         {β ιᵇ ρᵇ : Level} {B : Poset β ιᵇ ρᵇ}
         (R : Residuation A B)
         where


 private
  _≤A_ = _≤_ A
  _≤B_ = _≤_ B

  𝑓 = (R .f)
  𝑔 = (R .g)


  -- Pointwise equality of unary functions wrt equality
  -- on the given poset carrier
  -- 1. pointwise equality on B → A
  _≈̇A_ = PointWise{α = β}{A = Carrier B} (_≈_ A)
  -- 2. pointwise equality on A → B
  _≈̇B_ = PointWise{α = α}{A = Carrier A} (_≈_ B)

 lemma1 : (𝑓 ∘ 𝑔 ∘ 𝑓) ≈̇B 𝑓
 lemma1 a = antisym B lt gt
  where
  lt : 𝑓 (𝑔 (𝑓 a)) ≤B 𝑓 a
  lt = fg≤id R (𝑓 a)
  gt : 𝑓 a ≤B 𝑓 (𝑔 (𝑓 a))
  gt = fhom R (gf≥id R a)

 lemma2 : (𝑔 ∘ 𝑓 ∘ 𝑔) ≈̇A 𝑔
 lemma2 b = antisym A lt gt
  where
  lt : 𝑔 (𝑓 (𝑔 b)) ≤A 𝑔 b
  lt = ghom R (fg≤id R b)
  gt : 𝑔 b ≤A 𝑔 (𝑓 (𝑔 b))
  gt = gf≥id R (𝑔 b)

\end{code}
