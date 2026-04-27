---
layout: default
title : "Setoid.Functions.Basic module"
date : "2021-09-13"
author: "the agda-algebras development team"
---

### <a id="setoid-functions">Setoid functions</a>

This is the [Setoid.Functions.Basic][] module of the [Agda Universal Algebra Library][].


```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Functions.Basic where

-- Imports from Agda and the Agda Standard Library -----------------------
open import Agda.Primitive   using () renaming ( Set to Type )
open import Function         using ( id ; _∘_ ) renaming ( Func to _⟶_ )
open import Level            using ( Level ; Lift ; _⊔_ )
open import Relation.Binary  using ( Setoid )

private variable α ρᵃ β ρᵇ γ ρᶜ : Level

𝑖𝑑 : {A : Setoid α ρᵃ} → A ⟶ A
𝑖𝑑 {A} = record { to = id ; cong = id }

open _⟶_ renaming ( to to _⟨$⟩_ )

_⊙_ :  {A : Setoid α ρᵃ}{B : Setoid β ρᵇ}{C : Setoid γ ρᶜ}
 →     B ⟶ C → A ⟶ B → A ⟶ C
f ⊙ g = record { to = (_⟨$⟩_ f) ∘ (_⟨$⟩_ g); cong = (cong f) ∘ (cong g) }

module _ {𝑨 : Setoid α ρᵃ} where
 open Lift ; open Level ; open Setoid using (_≈_)
 open Setoid 𝑨 using ( sym ; trans ) renaming (Carrier to A ; _≈_ to _≈ₐ_ ; refl to reflₐ)

 𝑙𝑖𝑓𝑡 : ∀ ℓ → Setoid (α ⊔ ℓ) ρᵃ
 𝑙𝑖𝑓𝑡 ℓ = record  { Carrier = Lift ℓ A
                ; _≈_ = λ x y → (lower x) ≈ₐ (lower y)
                ; isEquivalence = record { refl = reflₐ ; sym = sym ; trans = trans }
                }

 lift∼lower : (a : Lift β A) → (_≈_ (𝑙𝑖𝑓𝑡 β)) (lift (lower a)) a
 lift∼lower a = reflₐ

 lower∼lift : ∀ a → (lower {α}{β}) (lift a) ≈ₐ a
 lower∼lift _ = reflₐ

 liftFunc : {ℓ : Level} → 𝑨 ⟶ 𝑙𝑖𝑓𝑡 ℓ
 liftFunc = record { to = lift ; cong = id }
```


--------------------------------------

<span style="float:left;">[↑ Setoid.Overture](Setoid.Overture.html)</span>
<span style="float:right;">[Setoid.Overture.Inverses →](Setoid.Overture.Inverses.html)</span>

{% include UALib.Links.md %}

