---
layout: default
title : "Overture.Setoid module (The Agda Universal Algebra Library)"
date : "2021-09-09"
author: "agda-algebras development team"
---

#### <a id="tools-for-working-with-setoids">Tools for working with setoids</a>

This is the [Overture.Setoid][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Overture.Setoid where

-- Imports from Agda and the Agda Standard Library -------------------------------------------------
open import Agda.Primitive                        using ( _⊔_ ) renaming ( Set to Type )
open import Level                                 using ( Level )
open import Relation.Binary                       using ( Setoid )
open import Relation.Binary.PropositionalEquality using (sym)

-- Imports from the Agda Universal Algebra Library ------------------------------------------------
open import Overture.Inverses                  using ( IsSurjective ; SurjInv ; Image_∋_ ; Inv )

private variable
 α ρᵃ β ρᵇ : Level

open Setoid hiding (sym)

preserves≈ : (𝑨 : Setoid α ρᵃ)(𝑩 : Setoid β ρᵇ)
 →           (Carrier 𝑨 → Carrier 𝑩) → Type (α ⊔ ρᵃ ⊔ ρᵇ)
preserves≈ 𝑨 𝑩 f = ∀ {x y} → (_≈_ 𝑨) x y → (_≈_ 𝑩) (f x) (f y)


module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where

 private
  _≈A≈_ = _≈_ 𝑨
  _≈B≈_ = _≈_ 𝑩
 open Image_∋_

 -- injectivity with respect to setoid equalities
 SInjective : (Carrier 𝑨 → Carrier 𝑩) → Type (α ⊔ ρᵃ ⊔ ρᵇ)
 SInjective f = ∀ a₀ a₁ → f a₀ ≈B≈ f a₁ → a₀ ≈A≈ a₁


 -- Inverse of an SInjective function preserves setoid equalities
 SInjInvPreserves≈ : (f : Carrier 𝑨 → Carrier 𝑩)(fi : SInjective f)
                    {b₀ b₁ : Carrier 𝑩}(u : Image f ∋ b₀)(v : Image f ∋ b₁)
  →                 b₀ ≈B≈ b₁ → (Inv f u) ≈A≈ (Inv f v)

 SInjInvPreserves≈ f fi {b₀}{b₁} (eq a₀ x₀) (eq a₁ x₁) bb = Goal
  where
  fa₀≈b₀ : f a₀ ≈B≈ b₀
  fa₀≈b₀ = reflexive 𝑩 (sym x₀)
  b₁≈fa₁ : b₁ ≈B≈ f a₁
  b₁≈fa₁ = reflexive 𝑩 x₁
  fa≈fa : f a₀ ≈B≈ f a₁
  fa≈fa = trans 𝑩 fa₀≈b₀ (trans 𝑩 bb b₁≈fa₁)
  Goal : a₀ ≈A≈ a₁
  Goal = fi a₀ a₁ fa≈fa


 -- Inverse of a function that is surjective and SInjective preserves setoid equalities
 BijInv-preserves≈ : (f : Carrier 𝑨 → Carrier 𝑩)(σ : IsSurjective f) → SInjective f
  →                   preserves≈ 𝑩 𝑨 (SurjInv f σ)
 BijInv-preserves≈ f σ fi {x}{y} xy = Goal
  where
  Goal : (Inv f (σ x)) ≈A≈ (Inv f (σ y))
  Goal = SInjInvPreserves≈ f fi (σ x) (σ y) xy

