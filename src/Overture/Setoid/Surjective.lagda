---
layout: default
title : "Overture.Setoid.Surjective module"
date : "2021-09-10"
author: "the agda-algebras development team"
---

### <a id="surjective-functions-on-setoids">Surjective functions on setoids</a>

This is the [Overture.Setoid.Surjective][] module of the [agda-algebras][] library.

A *surjective function* from a setoid `𝑨 = (A, ≈₀)` to a setoid `𝑩 = (B, ≈₁)` is a function `f : 𝑨 ⟶ 𝑩` such that for all `b : B` there exists `a : A` such that `(f ⟨$⟩ a) ≈₁ b`.  In other words, the range and codomain of `f` agree.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Relation.Binary using ( Setoid )

module Overture.Setoid.Surjective where

-- Imports from Agda and the Agda Standard Library --------------------------
open import Agda.Primitive    using ( _⊔_ ; Level ) renaming ( Set to Type )
open import Data.Product      using ( _,_ ; Σ-syntax ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Function.Bundles using ( Surjection ; RightInverse )
import      Function.Definitions as FunctionDefinitions
open import Function.Equality using ( Π ; _⟶_ ; _∘_ )
import      Function.Structures as FunctionStructures
open import Relation.Binary   using ( _Preserves_⟶_ ; _=[_]⇒_)

-- Imports from agda-algebras -----------------------------------------------
open import Overture.Preliminaries using ( ∣_∣ ; ∥_∥ ; ∃-syntax )
open import Overture.Setoid.Inverses using ( Image_∋_ ; Inv ; InvIsInv )

open Setoid
open Π

private variable
 α ℓ₁ β ℓ₂ γ ℓ₃ : Level

module _ {From : Setoid α ℓ₁}{To : Setoid β ℓ₂} where

 open Setoid From using () renaming (Carrier to A; _≈_ to _≈₁_)
 open Setoid To   using () renaming (Carrier to B; _≈_ to _≈₂_)
 open FunctionDefinitions _≈₁_ _≈₂_
 open FunctionStructures  _≈₁_ _≈₂_

 IsSurjective : (From ⟶ To) →  Type (α ⊔ β ⊔ ℓ₂)
 IsSurjective f = ∀ y → Image f ∋ y

 open Surjection
 open Image_∋_
 SurjectionIsSurjective : (Surjection From To) → Σ[ g ∈ (From ⟶ To) ] (IsSurjective g)
 SurjectionIsSurjective s = g , gE
  where
  g : From ⟶ To
  g = (record { _⟨$⟩_ = f s ; cong = cong s })
  gE : IsSurjective g
  gE y = eq ∣ (surjective s) y ∣ (sym To ∥ (surjective s) y ∥)


module _ {From : Setoid α ℓ₁}{To : Setoid β ℓ₂} where

 open Setoid From using () renaming (Carrier to A; _≈_ to _≈₁_)
 open Setoid To   using () renaming (Carrier to B; _≈_ to _≈₂_)
 open FunctionDefinitions _≈₁_ _≈₂_
 open FunctionStructures  _≈₁_ _≈₂_

 open Surjection renaming (f to sf )
 open RightInverse
 -- Surjection→RightInv : Surjection From To → RightInverse From To
 -- f (Surjection→RightInv s) = sf s
 -- g (Surjection→RightInv s) b = ∣ (surjective s) b ∣
 -- cong₁ (Surjection→RightInv s) = cong s
 -- cong₂ (Surjection→RightInv s) {x}{y} = g-preserves
 --  where
 --  g-preserves : x ≈₂ y → (∣ surjective s x ∣ ≈₁ ∣ surjective s y ∣)
 --  g-preserves x≈y = {!!}
 -- inverseʳ (Surjection→RightInv s) = {!!}

\end{code}

With the next definition, we can represent a *right-inverse* of a surjective function.

\begin{code}

 RightInv : (f : From ⟶ To) → IsSurjective f → B → A
 RightInv f fE b = Inv f (fE b)

\end{code}

Thus, a right-inverse of `f` is obtained by applying `RightInv` to `f` and a proof of `IsSurjective f`.  Next we prove that this does indeed give the right-inverse.

\begin{code}

 RightInvIsRightInv : (f : From ⟶ To)(fE : IsSurjective f) → ∀ b → (f ⟨$⟩ ((RightInv f fE) b)) ≈₂ b
 RightInvIsRightInv f fE b = InvIsInv f (fE b)

\end{code}

Next, we prove a composition law for epics.

\begin{code}

module _ {𝑨 : Setoid α ℓ₁}{𝑩 : Setoid β ℓ₂}{𝑪 : Setoid γ ℓ₃} where

 open Setoid 𝑨 using () renaming (Carrier to A; _≈_ to _≈₁_)
 open Setoid 𝑩 using () renaming (Carrier to B; _≈_ to _≈₂_)

 open Image_∋_

 epic-factor : (f : 𝑨 ⟶ 𝑩)(g : 𝑨 ⟶ 𝑪)(h : 𝑪 ⟶ 𝑩)
  →            IsSurjective f → (∀ i → (f ⟨$⟩ i) ≈₂ ((h ∘ g) ⟨$⟩ i)) → IsSurjective h

 epic-factor f g h fE compId y = Goal
  where
   finv : B → A
   finv = RightInv f fE

   ζ : y ≈₂ (f ⟨$⟩ (finv y))
   ζ = sym 𝑩 (RightInvIsRightInv f fE y)

   η : y ≈₂ ((h ∘ g) ⟨$⟩ (finv y))
   η = trans 𝑩 ζ (compId (finv y))

   Goal : Image h ∋ y
   Goal = eq (g ⟨$⟩ (finv y)) η
\end{code}


--------------------------------------

<span style="float:left;">[← Overture.Setoid.Injective](Overture.Setoid.Injective.html)</span>
<span style="float:right;">[Overture.Setoid.Bijective →](Overture.Setoid.Bijective.html)</span>

{% include UALib.Links.md %}

