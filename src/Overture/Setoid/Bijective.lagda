---
layout: default
title : "Overture.Setoid.Bijective module"
date : "2021-09-11"
author: "the agda-algebras development team"
---

### <a id="bijective-functions-on-setoids">Bijective functions on setoids</a>

This is the [Overture.Setoid.Bijective][] module of the [agda-algebras][] library.

A *bijective function* from a setoid `𝑨 = (A, ≈₀)` to a setoid `𝑩 = (B, ≈₁)` is a function `f : 𝑨 ⟶ 𝑩` that is both injective and surjective. (See the definitions in the modules [Overture.Setoid.Injective][] and [Overture.Setoid.Surjective][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Relation.Binary using ( Setoid )

module Overture.Setoid.Bijective where

-- Imports from Agda and the Agda Standard Library --------------------------
open import Agda.Primitive    using ( _⊔_ ; Level ) renaming ( Set to Type )
open import Data.Product      using ( _,_ ; _×_ )
open import Function.Equality using ( Π ; _⟶_ )

-- -- Imports from agda-algebras -----------------------------------------------
open import Overture.Setoid.Inverses using ( Image_∋_ ; Inv )
open import Overture.Setoid.Surjective using ( IsSurjective )
open import Overture.Setoid.Injective using ( IsInjective )

private variable
 α ρᵃ β ρᵇ : Level

module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where

 open Image_∋_

 open Setoid 𝑨 using () renaming (Carrier to A; _≈_ to _≈₁_)
 open Setoid 𝑩 using ( sym ; trans ) renaming (Carrier to B; _≈_ to _≈₂_)

 IsBijective : (𝑨 ⟶ 𝑩) → Type (α ⊔ β ⊔ ρᵃ ⊔ ρᵇ)
 IsBijective f = IsInjective f × IsSurjective f

 BijInv : (f : 𝑨 ⟶ 𝑩) → IsBijective f → 𝑩 ⟶ 𝑨
 BijInv f (fM , fE) = record { _⟨$⟩_ = finv ; cong = c }
  where
  finv : B → A
  finv b = Inv f (fE b)

  handler : ∀ {b₀ b₁}(i₀ : Image f ∋ b₀)(i₁ : Image f ∋ b₁)
   →        b₀ ≈₂ b₁ → (Inv f i₀) ≈₁ (Inv f i₁)

  handler (eq a x) (eq a₁ x₁) b₀≈b₁ = fM (trans (sym x) (trans b₀≈b₁ x₁))

  c : ∀ {b₀ b₁} → b₀ ≈₂ b₁ → (finv b₀) ≈₁ (finv b₁)
  c {b₀}{b₁} b₀≈b₁ = handler (fE b₀) (fE b₁) b₀≈b₁

\end{code}

------------------------------------

<span style="float:left;">[← Overture.Setoid.Surjective](Overture.Setoid.Surjective.html)</span>
<span style="float:right;">[Relations →](Relations.html)</span>

{% include UALib.Links.md %}

