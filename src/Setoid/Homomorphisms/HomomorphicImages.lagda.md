n---
layout: default
title : "Setoid.Homomorphisms.HomomorphicImages module (The Agda Universal Algebra Library)"
date : "2021-09-14"
author: "agda-algebras development team"
---

#### Homomorphic images of setoid algebras

This is the [Setoid.Homomorphisms.HomomorphicImages][] module of the [Agda Universal Algebra Library][].

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Homomorphisms.HomomorphicImages where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ----------------------------------------------------
open import Data.Product  renaming ( _×_ to _∧_ )  using ( _,_ ; Σ-syntax )
open import Function                               using ( Func ; _∘_ )
open import Level                                  using ( Level ; _⊔_ ; suc )
open import Relation.Binary                        using ( Setoid )
open import Relation.Unary                         using ( Pred ; _∈_ )
open import Relation.Binary.PropositionalEquality  using (refl)

-- Imports from the Agda Universal Algebra Library ---------------------------------------------
open import Overture                           using  ( proj₁ ; proj₂ ; ArityOf ; 𝑆 )
open import Setoid.Algebras                    using  ( Algebra ; ov ; _^_ ; 𝔻[_]
                                                      ; Lift-Algˡ ; Lift-Alg ; 𝕌[_] )
open import Setoid.Functions                   using  (IsSurjective; Image_∋_ ; Ran
                                                      ; range ; preimage ; image ; Inv
                                                      ; preimage≈image ; lift∼lower
                                                      ; InvIsInverseʳ ; ⊙-IsSurjective)
open import Setoid.Homomorphisms.Basic         using  ( hom ; IsHom ; 𝒾𝒹 )
open import Setoid.Homomorphisms.Isomorphisms  using  ( _≅_ ; Lift-≅ )
open import Setoid.Homomorphisms.Properties    using  ( Lift-homˡ ; ToLiftˡ
                                                      ; lift-hom-lemma ; ⊙-hom )
open import Setoid.Signatures                  using  ( ⟨_⟩ )

open Algebra

private variable α ρᵃ β ρᵇ : Level
```
-->

We begin with what seems, for our purposes, the most useful way to represent the
class of *homomorphic images* of an algebra in dependent type theory.

```agda
open IsHom

_IsHomImageOf_ : (𝑩 : Algebra {𝑆 = 𝑆} β ρᵇ)(𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ) → Type _
𝑩 IsHomImageOf 𝑨 = Σ[ (φ , _ ) ∈ hom 𝑨 𝑩 ] IsSurjective φ

HomImages : Algebra {𝑆 = 𝑆} α ρᵃ → Type (α ⊔ ρᵃ ⊔ ov {𝑆 = 𝑆} (β ⊔ ρᵇ))
HomImages {β = β}{ρᵇ} 𝑨 = Σ[ 𝑩 ∈ Algebra β ρᵇ ] 𝑩 IsHomImageOf 𝑨

IdHomImage : {𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ} → 𝑨 IsHomImageOf 𝑨
IdHomImage {𝑨 = 𝑨} = 𝒾𝒹 , λ {y} → Image_∋_.eq y (Setoid.refl 𝔻[ 𝑨 ])
```


These types should be self-explanatory, but just to be sure, let's describe the
Sigma type appearing in the second definition. Given an `𝑆`-algebra
`𝑨 : Algebra α ρ`, the type `HomImages 𝑨` denotes the class `𝒦` of algebras such
that `𝑩 ∈ 𝒦` provided there is a surjective homomorphism from `𝑨` to `𝑩`.

#### The image algebra of a hom

Here we show how to construct a Algebra (called `ImageAlgebra` below) that is
the image of given hom.


```agda
module _ {𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ}{𝑩 : Algebra {𝑆 = 𝑆} β ρᵇ} where
  open Algebra 𝑩  using () renaming (Domain to B ; Interp to InterpB )
  open Setoid B   using () renaming ( _≈_ to _≈₂_ ; trans to trans₂ )
  open Func       using ( cong ) renaming ( to to _⟨$⟩_ )

  HomImageOf[_] : hom 𝑨 𝑩 → Algebra {𝑆 = 𝑆} (α ⊔ β ⊔ ρᵇ) ρᵇ
  HomImageOf[ (h , hh) ] =
    record { Domain = Ran h ; Interp = record { to = f' ; cong = cong' } }
      where
      open Setoid(⟨ 𝑆 ⟩ (Ran h))
        using() renaming (Carrier to SRanh ; _≈_ to _≈₃_ )
      hhom :  ∀ {𝑓}(x : ArityOf 𝑆 𝑓 → range h)
        → h ⟨$⟩ (𝑓 ^ 𝑨) (preimage h ∘ x) ≈₂ (𝑓 ^ 𝑩) (image h ∘ x)

      hhom {𝑓} x = trans₂ (hh .compatible) (cong InterpB (refl , preimage≈image h ∘ x))

      f' : SRanh → range h
      f' (𝑓 , x) =  (𝑓 ^ 𝑩)(image h ∘ x)       -- b : the image in ∣B∣
                    , (𝑓 ^ 𝑨)(preimage h ∘ x)  -- a : the preimage in ∣A∣
                    , hhom x                   -- p : proof that h ⟨$⟩ a ≈₂ b

      cong' : ∀ {x y} → x ≈₃ y → (image h) (f' x) ≈₂ (image h) (f' y)
      cong' {(𝑓 , u)} {(.𝑓 , v)} (refl , EqA) = Goal
        where
        -- Alternative formulation of the goal:
        goal : (𝑓 ^ 𝑩)(λ i → (image h)(u i)) ≈₂ (𝑓 ^ 𝑩)(λ i → (image h) (v i))
        goal = cong InterpB (refl , EqA )

        Goal : (image h) (f' (𝑓 , u)) ≈₂ (image h) (f' (𝑓 , v))
        Goal = goal
        -- Note: `EqA : ∀ i → (image h) (u i) ≈₂ (image h) (v i)`
```


#### Homomorphic images of classes of setoid algebras

Given a class `𝒦` of `𝑆`-algebras, we need a type that expresses the assertion that a given algebra is a homomorphic image of some algebra in the class, as well as a type that represents all such homomorphic images.


```agda
IsHomImageOfClass : {𝒦 : Pred (Algebra {𝑆 = 𝑆} α ρᵃ)(suc α)} → Algebra {𝑆 = 𝑆} α ρᵃ → Type (ov {𝑆 = 𝑆} (α ⊔ ρᵃ))
IsHomImageOfClass {𝒦 = 𝒦} 𝑩 = Σ[ 𝑨 ∈ Algebra _ _ ] ((𝑨 ∈ 𝒦) ∧ (𝑩 IsHomImageOf 𝑨))

HomImageOfClass : Pred (Algebra {𝑆 = 𝑆} α ρᵃ) (suc α) → Type (ov {𝑆 = 𝑆} (α ⊔ ρᵃ))
HomImageOfClass 𝒦 = Σ[ 𝑩 ∈ Algebra _ _ ] IsHomImageOfClass {𝒦 = 𝒦} 𝑩
```

#### Lifting tools

Here are some tools that have been useful (e.g., in the road to the proof of
Birkhoff's HSP theorem). The first states and proves the simple fact that the lift of
an epimorphism is an epimorphism.

```agda
module _ {𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ}{𝑩 : Algebra {𝑆 = 𝑆} β ρᵇ} where
  open Setoid 𝔻[ 𝑩 ]   using ( sym ; trans )  renaming ( _≈_ to _≈₂_ )
  open Func       using ( cong )         renaming ( to to _⟨$⟩_ )
  open Level      using ( lift ; lower )

  Lift-epi-is-epiˡ :  (h : hom 𝑨 𝑩)(ℓᵃ ℓᵇ : Level)
    → IsSurjective (proj₁ h) → IsSurjective (proj₁ (Lift-homˡ {𝑨 = 𝑨}{𝑩} h ℓᵃ ℓᵇ))

  Lift-epi-is-epiˡ h ℓᵃ ℓᵇ hepi {b} = Goal
    where
    open Setoid 𝔻[ Lift-Algˡ 𝑩 ℓᵇ ] using ( _≈_ )

    a : 𝕌[ 𝑨 ]
    a = Inv (h .proj₁) hepi

    lem1 : b ≈ lift (lower b)
    lem1 = lift∼lower {𝑨 = 𝔻[ 𝑩 ]} b

    lem2' : lower b ≈₂ h .proj₁ ⟨$⟩ a
    lem2' = sym  (InvIsInverseʳ hepi)

    lem2 : lift (lower b) ≈ lift (h .proj₁ ⟨$⟩ a)
    lem2 = cong{From = 𝔻[ 𝑩 ]} (ToLiftˡ{𝑨 = 𝑩}{ℓᵇ} .proj₁) lem2'

    lem3 : lift (h .proj₁ ⟨$⟩ a) ≈ (Lift-homˡ h ℓᵃ ℓᵇ) .proj₁ ⟨$⟩ lift a
    lem3 = lift-hom-lemma h a ℓᵃ ℓᵇ

    η : b ≈ (Lift-homˡ h ℓᵃ ℓᵇ) .proj₁ ⟨$⟩ lift a
    η = trans lem1 (trans lem2 lem3)

    Goal : Image (Lift-homˡ h ℓᵃ ℓᵇ) .proj₁ ∋ b
    Goal = Image_∋_.eq (lift a) η


  Lift-Alg-hom-imageˡ :  (ℓᵃ ℓᵇ : Level) → 𝑩 IsHomImageOf 𝑨
    → (Lift-Algˡ 𝑩 ℓᵇ) IsHomImageOf (Lift-Algˡ 𝑨 ℓᵃ)

  Lift-Alg-hom-imageˡ ℓᵃ ℓᵇ ((φ , φhom) , φepic) = Goal
    where
    lφ : hom (Lift-Algˡ 𝑨 ℓᵃ) (Lift-Algˡ 𝑩 ℓᵇ)
    lφ = Lift-homˡ {𝑨 = 𝑨}{𝑩} (φ , φhom) ℓᵃ ℓᵇ

    lφepic : IsSurjective (lφ .proj₁)
    lφepic = Lift-epi-is-epiˡ (φ , φhom) ℓᵃ ℓᵇ φepic
    Goal : (Lift-Algˡ 𝑩 ℓᵇ) IsHomImageOf (Lift-Algˡ 𝑨 ℓᵃ)
    Goal = lφ , lφepic


module _ {𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ}{𝑩 : Algebra {𝑆 = 𝑆} β ρᵇ} where
  open _≅_
  Lift-HomImage-lemma : ∀{γ} → (Lift-Alg 𝑨 γ γ) IsHomImageOf 𝑩 → 𝑨 IsHomImageOf 𝑩
  Lift-HomImage-lemma {γ} φ =  ⊙-hom (φ .proj₁) (from Lift-≅) ,
                               ⊙-IsSurjective (φ .proj₂) (fromIsSurjective (Lift-≅{𝑨 = 𝑨}))

module _ {𝑨 𝑨' : Algebra {𝑆 = 𝑆} α ρᵃ}{𝑩 : Algebra {𝑆 = 𝑆} β ρᵇ} where
  open _≅_
  HomImage-≅ : 𝑨 IsHomImageOf 𝑨' → 𝑨 ≅ 𝑩 → 𝑩 IsHomImageOf 𝑨'
  HomImage-≅ φ A≅B = ⊙-hom (φ .proj₁) (to A≅B) , ⊙-IsSurjective (φ .proj₂) (toIsSurjective A≅B)

  HomImage-≅' : 𝑨 IsHomImageOf 𝑨' → 𝑨' ≅ 𝑩 → 𝑨 IsHomImageOf 𝑩
  HomImage-≅' φ A'≅B = (⊙-hom (from A'≅B) (proj₁ φ)) , ⊙-IsSurjective (fromIsSurjective A'≅B) (φ .proj₂)
```
