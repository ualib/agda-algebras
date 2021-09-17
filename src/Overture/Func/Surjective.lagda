n---
layout: default
title : "Overture.Func.Surjective module"
date : "2021-09-13"
author: "the agda-algebras development team"
---

### <a id="surjective-functions-on-setoids">Surjective functions on setoids</a>

This is the [Overture.Func.Surjective][] module of the [agda-algebras][] library.

A *surjective function* from a setoid `𝑨 = (A, ≈₀)` to a setoid `𝑩 = (B, ≈₁)` is a function `f : 𝑨 ⟶ 𝑩` such that for all `b : B` there exists `a : A` such that `(f ⟨$⟩ a) ≈₁ b`.  In other words, the range and codomain of `f` agree.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Relation.Binary using ( Setoid )

module Overture.Func.Surjective where

-- Imports from Agda and the Agda Standard Library --------------------------
open import Agda.Primitive   using ( _⊔_ ; Level ) renaming ( Set to Type )
open import Data.Product     using ( _,_ ; Σ-syntax )
open import Function.Bundles using ( Func ; Surjection )
import Function.Definitions as FD

-- Imports from agda-algebras -----------------------------------------------
open import Overture.Preliminaries      using ( ∣_∣ ; ∥_∥ ; ∃-syntax )
open import Overture.Func.Preliminaries using ( _⟶_ ; _∘_ )
open import Overture.Func.Inverses      using ( Image_∋_ ; Inv ; InvIsInverseʳ )

private variable
 α ρᵃ β ρᵇ γ ρᶜ : Level


module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where

 open Surjection {a = α}{ρᵃ}{β}{ρᵇ}{From = 𝑨}{To = 𝑩} renaming (f to _⟨$⟩_)
 open Setoid 𝑨 using () renaming (Carrier to A; _≈_ to _≈₁_)
 open Setoid 𝑩 using ( trans ; sym ) renaming (Carrier to B; _≈_ to _≈₂_)
 open Func {a = α}{ρᵃ}{β}{ρᵇ}{From = 𝑨}{To = 𝑩} renaming (f to _⟨$⟩_ )
 open FD _≈₁_ _≈₂_

 IsSurjective : (𝑨 ⟶ 𝑩) →  Type (α ⊔ β ⊔ ρᵇ)
 IsSurjective f = ∀ {y} → Image f ∋ y  -- Surjective (_⟨$⟩_ f)

 open Image_∋_

 SurjectionIsSurjective : (Surjection 𝑨 𝑩) → Σ[ g ∈ (𝑨 ⟶ 𝑩) ] (IsSurjective g)
 SurjectionIsSurjective s = g , gE
  where
  g : 𝑨 ⟶ 𝑩
  g = (record { f = _⟨$⟩_ s ; cong = cong s })
  gE : IsSurjective g
  gE {y} = eq ∣ (surjective s) y ∣ (sym ∥ (surjective s) y ∥)

\end{code}

With the next definition, we can represent a *right-inverse* of a surjective function.

\begin{code}

 SurjInv : (f : 𝑨 ⟶ 𝑩) → IsSurjective f → B → A
 SurjInv f fE b = Inv f (fE {b})

\end{code}

Thus, a right-inverse of `f` is obtained by applying `RightInv` to `f` and a proof of `IsSurjective f`.  Next we prove that this does indeed give the right-inverse.

\begin{code}

 SurjInvIsInverseʳ : (f : 𝑨 ⟶ 𝑩)(fE : IsSurjective f) → ∀ {b} → (f ⟨$⟩ ((SurjInv f fE) b)) ≈₂ b
 SurjInvIsInverseʳ f fE = InvIsInverseʳ fE

\end{code}

Next, we prove a composition law for epics.

\begin{code}

module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ}{𝑪 : Setoid γ ρᶜ} where

 open Surjection {a = α}{ρᵃ}{β}{ρᵇ}{From = 𝑨}{To = 𝑩} renaming (f to _⟨$⟩_)
 open Setoid 𝑨 using () renaming (Carrier to A; _≈_ to _≈₁_)
 open Setoid 𝑩 using ( trans ; sym ) renaming (Carrier to B; _≈_ to _≈₂_)
 open Setoid 𝑪 using () renaming (Carrier to C; _≈_ to _≈₃_)
 open Func {a = α}{ρᵃ}{β}{ρᵇ}{From = 𝑨}{To = 𝑩} renaming (f to _⟨$⟩_ )
 open FD _≈₁_ _≈₂_
 open Image_∋_

 epic-factor : (f : 𝑨 ⟶ 𝑩)(g : 𝑨 ⟶ 𝑪)(h : 𝑪 ⟶ 𝑩)
  →            IsSurjective f → (∀ i → (f ⟨$⟩ i) ≈₂ ((h ∘ g) ⟨$⟩ i)) → IsSurjective h

 epic-factor f g h fE compId {y} = Goal
  where
   finv : B → A
   finv = SurjInv f fE

   ζ : y ≈₂ (f ⟨$⟩ (finv y))
   ζ = sym (SurjInvIsInverseʳ f fE)

   η : y ≈₂ ((h ∘ g) ⟨$⟩ (finv y))
   η = trans ζ (compId (finv y))

   Goal : Image h ∋ y
   Goal = eq (g ⟨$⟩ (finv y)) η
\end{code}


--------------------------------------

<span style="float:left;">[← Overture.Func.Injective](Overture.Func.Injective.html)</span>
<span style="float:right;">[Overture.Func.Bijective →](Overture.Func.Bijective.html)</span>

{% include UALib.Links.md %}

