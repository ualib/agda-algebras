---
layout: default
title : "Setoid.Overture.Preliminaries module"
date : "2021-09-13"
author: "the agda-algebras development team"
---

### <a id="preliminaries-for-setoids">Preliminaries for setoids</a>

This is the [Setoid.Overture.Preliminaries][] module of the [agda-algebras][] library.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


module Setoid.Overture.Preliminaries where

-- Imports from Agda and the Agda Standard Library -----------------------
open import Agda.Primitive    using ( _⊔_ ) renaming ( Set to Type )
open import Function          using ( id )
open import Function.Bundles  using () renaming ( Func to _⟶_ )
open import Relation.Binary   using ( Setoid )
open import Level

import Function.Base as Fun
private variable
 α ρᵃ β ρᵇ γ ρᶜ : Level

𝑖𝑑 : {A : Setoid α ρᵃ} → A ⟶ A
𝑖𝑑 {A} = record { f = id ; cong = id }

open _⟶_ renaming ( f to _⟨$⟩_ )

_∘_ : {A : Setoid α ρᵃ}
      {B : Setoid β ρᵇ}
      {C : Setoid γ ρᶜ}
 →    B ⟶ C → A ⟶ B → A ⟶ C
f ∘ g = record { f = Fun._∘_ (_⟨$⟩_ f) (_⟨$⟩_ g)
               ; cong = Fun._∘_ (cong f) (cong g)
               }


module _ {𝑨 : Setoid α ρᵃ} where
 open Setoid using (_≈_)
 open Setoid 𝑨 using ( sym ; trans ) renaming (Carrier to A ; _≈_ to _≈ₐ_ ; refl to reflₐ)

 𝑙𝑖𝑓𝑡 : ∀ ℓ → Setoid (α ⊔ ℓ) ρᵃ
 𝑙𝑖𝑓𝑡 ℓ = record { Carrier = Lift ℓ A
               ; _≈_ = λ x y → (lower x) ≈ₐ (lower y)
               ; isEquivalence = record { refl = reflₐ ; sym = sym ; trans = trans }
               }

 lift∼lower : (a : Lift β A) → (_≈_ (𝑙𝑖𝑓𝑡 β)) (lift (lower a)) a
 lift∼lower a = reflₐ

 lower∼lift : ∀ a → (lower {α}{β}) (lift a) ≈ₐ a
 lower∼lift _ = reflₐ

 liftFunc : {ℓ : Level} → 𝑨 ⟶ 𝑙𝑖𝑓𝑡 ℓ
 liftFunc = record { f = lift ; cong = id }

 module _ {𝑩 : Setoid β ρᵇ} where
  open Setoid 𝑩 using ( sym ) renaming (Carrier to B; _≈_ to _≈₂_)

  -- This is sometimes known as `cong` (see e.g. `Function.Equality` in the agda-stdlib)
  -- preserves≈ : (A → B) → Type (α ⊔ ρᵃ ⊔ ρᵇ)
  -- preserves≈ f = ∀ {x y} → x ≈ₐ y → (f x) ≈₂ (f y)

\end{code}

--------------------------------------

<span style="float:left;">[↑ Setoid.Overture](Setoid.Overture.html)</span>
<span style="float:right;">[Setoid.Overture.Inverses →](Setoid.Overture.Inverses.html)</span>

{% include UALib.Links.md %}

