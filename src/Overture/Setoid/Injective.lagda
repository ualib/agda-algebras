---
layout: default
title : "Overture.Setoid.Injective module"
date : "2021-09-10"
author: "the agda-algebras development team"
---

### <a id="injective-functions-on-setoids">Injective functions on setoids</a>

This is the [Overture.Setoid.Injective][] module of the [agda-algebras][] library.

We say that a function `f : A → B` from one setoid (A , ≈₀) to another (B , ≈₁) is *injective* (or *monic*) provided the following implications hold:  ∀ a₀ a₁ if f ⟨$⟩ a₀ ≈₁ f ⟨$⟩ a₁, then a₀ ≈₀ a₁.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Overture.Setoid.Injective where

-- Imports from Agda and the Agda Standard Library -------------
open import Agda.Primitive              using ( _⊔_ ; Level ) renaming ( Set to Type )
open import Function.Equality using ( Π ; _⟶_ ; _∘_ )
import      Function.Definitions as FunctionDefinitions
import      Function.Structures as FunctionStructures
open import Relation.Binary             using ( Setoid )
open import Function.Bundles            using ( Injection )
open import Relation.Binary.Core        using ( _Preserves_⟶_ )

-- Imports from agda-algebras -----------------------------------------------
open import Overture.FuncInverses using ( Image_∋_ ; Inv )
open import Overture.Injective as SetInjective using (module compose)
open Setoid using ( sym ; trans )


private variable
 α ρᵃ β ρᵇ γ ρᶜ : Level

module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where

 open Setoid 𝑨 using () renaming (Carrier to A; _≈_ to _≈₁_)
 open Setoid 𝑩 using () renaming (Carrier to B; _≈_ to _≈₂_)
 open FunctionDefinitions _≈₁_ _≈₂_
 open FunctionStructures  _≈₁_ _≈₂_

\end{code}

We can prove that, when `f` is injective, the range-restricted right-inverse `Inv`, defined in [Overture.Setoid.Inverse][], is also the (range-restricted) left-inverse.

\begin{code}

 open Image_∋_
 open Injection {a = α}{ρᵃ}{β}{ρᵇ}{From = 𝑨}{To = 𝑩} renaming (f to _⟨$⟩_)
 open Π
 IsInjective : (𝑨 ⟶ 𝑩) →  Type (α ⊔ ρᵃ ⊔ ρᵇ)
 IsInjective f = Injective (_⟨$⟩_ f) -- ∀ y → Image f ∋ y



 -- LeftInv : (f : 𝑨 ⟶ 𝑩) → Injection 𝑨 𝑩 → ∀ a a'
 --  → (p : (f ⟨$⟩ a) ≈₂ (f ⟨$⟩ a')) → (Inv f {f ⟨$⟩ a} (eq a' p)) ≈₁ a
 -- LeftInv f fM a a' p = injective fM {!p!} -- fM (sym 𝑩 p)

 -- InjInvIsLeftInv : {fi : Injection 𝑨 𝑩}{a : A}
 --  → (Inv (function fi) {(function fi) ⟨$⟩ a}) ≈₁ a
 -- InjInvIsLeftInv {fi} = ? -- injective fM {!p!} -- fM (sym 𝑩 p)

 -- Inverse of an injective function preserves setoid equalities
 LeftInvPreserves≈ : (F : Injection 𝑨 𝑩)
                     {b₀ b₁ : B}(u : Image (function F) ∋ b₀)(v : Image (function F) ∋ b₁)
  →                  b₀ ≈₂ b₁ → (Inv (function F) u) ≈₁ (Inv (function F) v)

 LeftInvPreserves≈ F {b₀}{b₁} (eq a₀ x₀) (eq a₁ x₁) bb = Goal
  where
  fa₀≈fa₁ : (F ⟨$⟩ a₀) ≈₂ (F ⟨$⟩ a₁)
  fa₀≈fa₁ = trans 𝑩 (sym 𝑩 x₀) (trans 𝑩 bb x₁)
  Goal : a₀ ≈₁ a₁
  Goal = injective F fa₀≈fa₁


 -- Composition is injective.
 module _ {𝑪 : Setoid γ ρᶜ} where
  open Setoid 𝑪 using ( sym ) renaming (Carrier to C; _≈_ to _≈₃_)

  open compose {A = A}{B}{C} _≈₁_ _≈₂_ _≈₃_ using ( ∘-injective )

  ∘-injection : Injection 𝑨 𝑩 → Injection 𝑩 𝑪 → Injection 𝑨 𝑪
  ∘-injection fi gi = record { f = λ x → apg (apf x)
                             ; cong = conggf
                             ; injective = ∘-injective (injective fi) (injective gi)
                             }
    where
    open Injection
    apf : A → B
    apf = f fi
    apg : B → C
    apg = f gi
    conggf : (λ x → apg (apf x)) Preserves _≈₁_ ⟶ _≈₃_
    conggf {x}{y} x≈y = cong gi (cong fi x≈y)

\end{code}

--------------------------------------

<span style="float:left;">[← Overture.Setoid.Inverses](Overture.Setoid.Inverses.html)</span>
<span style="float:right;">[Overture.Setoid.Surjective →](Overture.Setoid.Surjective.html)</span>

{% include UALib.Links.md %}

