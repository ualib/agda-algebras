---
layout: default
title : "Overture.Func.Preliminaries module"
date : "2021-09-13"
author: "the agda-algebras development team"
---

### <a id="preliminaries-for-setoids">Preliminaries for setoids</a>

This is the [Overture.Func.Preliminaries][] module of the [agda-algebras][] library.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


module Overture.Func.Preliminaries where

-- Imports from Agda and the Agda Standard Library -----------------------
open import Agda.Primitive          using ( _⊔_ ) renaming ( Set to Type )
open import Function                using ( id )
open import Function.Bundles        using ( Func )
import Function.Base as Fun
open import Relation.Binary         using ( Setoid )
open import Level

private variable
 α ρᵃ β ρᵇ γ ρᶜ : Level

open Setoid

_⟶_ : Setoid α ρᵃ → Setoid β ρᵇ → Type _
A ⟶ B = Func A B

𝑖𝑑 : {A : Setoid α ρᵃ} → A ⟶ A
𝑖𝑑 {A} = record { f = id ; cong = id }

open Func renaming ( f to _⟨$⟩_ )

_∘_ : {A : Setoid α ρᵃ}
      {B : Setoid β ρᵇ}
      {C : Setoid γ ρᶜ}
 →    B ⟶ C → A ⟶ B → A ⟶ C
f ∘ g = record { f = Fun._∘_ (_⟨$⟩_ f) (_⟨$⟩_ g)
               ; cong = Fun._∘_ (cong f) (cong g)
               }


module _ {𝑨 : Setoid α ρᵃ} where
 open Setoid 𝑨 using ( ) renaming (Carrier to A ; _≈_ to _≈₁_ )

 𝑙𝑖𝑓𝑡 : ∀ ℓ → Setoid (α ⊔ ℓ) ρᵃ
 𝑙𝑖𝑓𝑡 ℓ = record { Carrier = Lift ℓ A
               ; _≈_ = λ x y → (lower x) ≈₁ (lower y)
               ; isEquivalence = record { refl = refl 𝑨 ; sym = sym 𝑨 ; trans = trans 𝑨 }
               }

 lift∼lower : (a : Lift β A) → (_≈_ (𝑙𝑖𝑓𝑡 β)) (lift (lower a)) a
 lift∼lower a = refl 𝑨

 lower∼lift : ∀ a → (lower {α}{β}) (lift a) ≈₁ a
 lower∼lift _ = refl 𝑨

 liftFunc : {ℓ : Level} → Func 𝑨 (𝑙𝑖𝑓𝑡 ℓ)
 liftFunc = record { f = lift ; cong = id }

 module _ {𝑩 : Setoid β ρᵇ} where
  open Setoid 𝑩 using ( sym ) renaming (Carrier to B; _≈_ to _≈₂_)

  -- This is sometimes known as `cong` (see e.g. `Function.Equality` in the agda-stdlib)
  preserves≈ : (A → B) → Type (α ⊔ ρᵃ ⊔ ρᵇ)
  preserves≈ f = ∀ {x y} → x ≈₁ y → (f x) ≈₂ (f y)

\end{code}

--------------------------------------

<span style="float:left;">[↑ Overture.Func](Overture.Func.html)</span>
<span style="float:right;">[Overture.Func.Inverses →](Overture.Func.Inverses.html)</span>

{% include UALib.Links.md %}


