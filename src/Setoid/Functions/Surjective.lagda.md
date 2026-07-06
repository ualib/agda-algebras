---
layout: default
title : "Setoid.Functions.Surjective module"
date : "2021-09-13"
author: "the agda-algebras development team"
---

### Surjective functions on setoids

This is the [Setoid.Functions.Surjective][] module of the [agda-algebras][] library.

A *surjective function* from a setoid `𝑨 = (A, ≈₀)` to a setoid `𝑩 = (B, ≈₁)` is a function `f : 𝑨 ⟶ 𝑩` such that for all `b : B` there exists `a : A` such that `(f ⟨$⟩ a) ≈₁ b`.  In other words, the range and codomain of `f` agree.


```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Functions.Surjective where

-- Imports from Agda and the Agda Standard Library --------------------------
open import Agda.Primitive   using () renaming ( Set to Type )
open import Data.Product     using ( _,_ ; Σ-syntax )
open import Function         using ( Surjection ; IsSurjection ; _$_ ; _∘_ )
                             renaming ( Func to _⟶_ )
open import Level            using ( _⊔_ ; Level )
open import Relation.Binary  using ( Setoid ; IsEquivalence )

open import Function.Construct.Composition renaming ( isSurjection to isOnto )
 using ()

import Function.Definitions as FD

-- Imports from agda-algebras -----------------------------------------------
open import Overture                   using ( proj₁ ; proj₂ )
open import Setoid.Functions.Basic     using ( _⊙_ )
open import Setoid.Functions.Inverses  using ( Img_∋_ ; Image_∋_ ; Inv ; InvIsInverseʳ )


private variable
  α ρᵃ β ρᵇ γ ρᶜ : Level

open Image_∋_

module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where

  open Setoid 𝑨  renaming (Carrier to A; _≈_ to _≈₁_; isEquivalence to isEqA ) using ()
  open Setoid 𝑩  renaming (Carrier to B; _≈_ to _≈₂_; isEquivalence to isEqB )
                 using ( trans ; sym )

  open Surjection {a = α}{ρᵃ}{β}{ρᵇ}{From = 𝑨}{To = 𝑩}  renaming (to to _⟨$⟩_)
  open _⟶_ {a = α}{ρᵃ}{β}{ρᵇ}{From = 𝑨}{To = 𝑩}         renaming (to to _⟨$⟩_ )
  open FD

  isSurj : (A → B) → Type (α ⊔ β ⊔ ρᵇ)
  isSurj f = ∀ {y} → Img_∋_ {𝑨 = 𝑨}{𝑩 = 𝑩} f y

  IsSurjective : (𝑨 ⟶ 𝑩) → Type (α ⊔ β ⊔ ρᵇ)
  IsSurjective F = ∀ {y} → Image F ∋ y

  isSurj→IsSurjective : (F : 𝑨 ⟶ 𝑩) → isSurj (_⟨$⟩_ F) → IsSurjective F
  isSurj→IsSurjective F isSurjF {y} = hyp isSurjF
    where
    hyp : Img (_⟨$⟩_ F) ∋ y → Image F ∋ y
    hyp (Img_∋_.eq a x) = eq a x

  open Image_∋_

  SurjectionIsSurjective : (Surjection 𝑨 𝑩) → Σ[ g ∈ (𝑨 ⟶ 𝑩) ] (IsSurjective g)
  SurjectionIsSurjective s = g , gE
    where
    g : 𝑨 ⟶ 𝑩
    g = (record { to = _⟨$⟩_ s ; cong = cong s })
    gE : IsSurjective g
    gE {y} = eq (proj₁ ((surjective s) y)) (sym (proj₂ (surjective s y) (IsEquivalence.refl isEqA)))

  SurjectionIsSurjection : (Surjection 𝑨 𝑩) → Σ[ g ∈ (𝑨 ⟶ 𝑩) ] (IsSurjection _≈₁_ _≈₂_ (_⟨$⟩_ g))
  SurjectionIsSurjection s = g , gE
    where
    g : 𝑨 ⟶ 𝑩
    g = record { to = _⟨$⟩_ s ; cong = cong s }

    gE : IsSurjection _≈₁_ _≈₂_ (_⟨$⟩_ g)
    gE .IsSurjection.isCongruent = record  { cong = cong g
                                           ; isEquivalence₁ = isEqA
                                           ; isEquivalence₂ = isEqB
                                           }
    gE .IsSurjection.surjective y = (proj₁ ((surjective s) y)) , (proj₂ ((surjective s) y))
```


With the next definition we represent a *right-inverse* of a surjective setoid function.


```agda
  SurjInv : (f : 𝑨 ⟶ 𝑩) → IsSurjective f → B → A
  SurjInv f fE b = Inv f (fE {b})
```


Thus, a right-inverse of `f` is obtained by applying `Inv` to `f` and a proof of `IsSurjective f`.  Next we prove that this does indeed give the right-inverse.


```agda
  SurjInvIsInverseʳ :  (f : 𝑨 ⟶ 𝑩)(fE : IsSurjective f)
   →                   ∀ {b} → f ⟨$⟩ (SurjInv f fE) b ≈₂ b

  SurjInvIsInverseʳ f fE = InvIsInverseʳ fE
```


Next, we prove composition laws for epics.


```agda
module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ}{𝑪 : Setoid γ ρᶜ} where

  open Setoid 𝑨  using ()               renaming (Carrier to A; _≈_ to _≈₁_)
  open Setoid 𝑩  using ( trans ; sym )  renaming (Carrier to B; _≈_ to _≈₂_)
  open Surjection  renaming (to to _⟨$⟩_)
  open _⟶_         renaming (to to _⟨$⟩_ )
  open FD


  ⊙-IsSurjective :  {G : 𝑨 ⟶ 𝑪}{H : 𝑪 ⟶ 𝑩}
   →                IsSurjective G → IsSurjective H → IsSurjective (H ⊙ G)

  ⊙-IsSurjective {G} {H} gE hE {y} = Goal
    where
    mp : Image H ∋ y → Image H ⊙ G ∋ y
    mp (eq c p) = η gE
      where
      η : Image G ∋ c → Image H ⊙ G ∋ y
      η (eq a q) = eq a $ trans p $ cong H q

    Goal : Image H ⊙ G ∋ y
    Goal = mp hE


  ∘-epic : Surjection 𝑨 𝑪 → Surjection 𝑪 𝑩 → Surjection 𝑨 𝑩
  Surjection.to           (∘-epic g h) = h ⟨$⟩_ ∘ g ⟨$⟩_
  Surjection.cong        (∘-epic g h) = cong h ∘ cong g
  Surjection.surjective  (∘-epic g h) = surjective $ isOnto  (proj₂ (SurjectionIsSurjection g))
                                                             (proj₂ (SurjectionIsSurjection h))
   where open IsSurjection


  epic-factor :  (f : 𝑨 ⟶ 𝑩)(g : 𝑨 ⟶ 𝑪)(h : 𝑪 ⟶ 𝑩)
   →             IsSurjective f → (∀ i → (f ⟨$⟩ i) ≈₂ ((h ⊙ g) ⟨$⟩ i)) → IsSurjective h

  epic-factor f g h fE compId {y} = Goal
    where
     finv : B → A
     finv = SurjInv f fE

     ζ : y ≈₂ (f ⟨$⟩ (finv y))
     ζ = sym $ SurjInvIsInverseʳ f fE

     η : y ≈₂ ((h ⊙ g) ⟨$⟩ (finv y))
     η = trans ζ $ compId $ finv y

     Goal : Image h ∋ y
     Goal = eq (g ⟨$⟩ (finv y)) η
```
