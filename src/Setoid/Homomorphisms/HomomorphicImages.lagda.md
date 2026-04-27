---
layout: default
title : "Setoid.Homomorphisms.HomomorphicImages module (The Agda Universal Algebra Library)"
date : "2021-09-14"
author: "agda-algebras development team"
---

#### <a id="homomorphic-images-of-setoid-algebras">Homomorphic images of setoid algebras</a>

This is the [Setoid.Homomorphisms.HomomorphicImages][] module of the [Agda Universal Algebra Library][].


```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Homomorphisms.HomomorphicImages {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ------------------------------------------
open import Agda.Primitive   using () renaming ( Set to Type )
open import Data.Product     using ( _,_ ; Σ-syntax )
                             renaming ( _×_ to _∧_ ; proj₁ to fst ; proj₂ to snd )
open import Function         using ( Func ; _on_ ; _∘_ ; id )
open import Level            using ( Level ; _⊔_ ; suc )
open import Relation.Binary  using ( Setoid ; _Preserves_⟶_ )
open import Relation.Unary   using ( Pred ; _∈_ )

open import Relation.Binary.PropositionalEquality as ≡ using ()

-- Imports from the Agda Universal Algebra Library ---------------------------------------------
open import Overture          using  ( ∣_∣ ; ∥_∥ ; transport )
open  import Setoid.Functions
      using ( lift∼lower ; Ran ; _range ; _preimage ; _image ; Inv ; Image_∋_ )
      using ( _preimage≈image ; InvIsInverseʳ ; IsSurjective ; ⊙-IsSurjective )

open  import Setoid.Algebras {𝑆 = 𝑆}
      using ( Algebra ; ov ; _̂_ ; ⟨_⟩ ; Lift-Algˡ ; Lift-Alg ; 𝕌[_] )

open import Setoid.Homomorphisms.Basic {𝑆 = 𝑆}         using ( hom ; IsHom )
open import Setoid.Homomorphisms.Isomorphisms {𝑆 = 𝑆}  using ( _≅_ ; Lift-≅ )

open  import Setoid.Homomorphisms.Properties {𝑆 = 𝑆}
      using ( Lift-homˡ ; ToLiftˡ ; lift-hom-lemma ; 𝒾𝒹 ; ⊙-hom )

open Algebra

private variable α ρᵃ β ρᵇ : Level
```


We begin with what seems, for our purposes, the most useful way to represent the
class of *homomorphic images* of an algebra in dependent type theory.


```agda


open IsHom

_IsHomImageOf_ : (𝑩 : Algebra β ρᵇ)(𝑨 : Algebra α ρᵃ) → Type _
𝑩 IsHomImageOf 𝑨 = Σ[ φ ∈ hom 𝑨 𝑩 ] IsSurjective ∣ φ ∣

HomImages : Algebra α ρᵃ → Type (α ⊔ ρᵃ ⊔ ov (β ⊔ ρᵇ))
HomImages {β = β}{ρᵇ = ρᵇ} 𝑨 = Σ[ 𝑩 ∈ Algebra β ρᵇ ] 𝑩 IsHomImageOf 𝑨

IdHomImage : {𝑨 : Algebra α ρᵃ} → 𝑨 IsHomImageOf 𝑨
IdHomImage {α = α}{𝑨 = 𝑨} = 𝒾𝒹 , λ {y} → Image_∋_.eq y refl
 where open Setoid (Domain 𝑨) using ( refl )
```


These types should be self-explanatory, but just to be sure, let's describe the
Sigma type appearing in the second definition. Given an `𝑆`-algebra
`𝑨 : Algebra α ρ`, the type `HomImages 𝑨` denotes the class `𝒦` of algebras such
that `𝑩 ∈ 𝒦` provided there is a surjective homomorphism from `𝑨` to `𝑩`.

#### <a id="constructing an algebra from the image of a hom">The image algebra of a hom</a>

Here we show how to construct a Algebra (called `ImageAlgebra` below) that is
the image of given hom.


```agda


module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} where
 open Algebra 𝑨  renaming (Domain to A )                      using (Interp)
 open Setoid A   renaming ( _≈_ to _≈₁_ ; Carrier to ∣A∣)     using ()
 open Algebra 𝑩  renaming (Domain to B ; Interp to InterpB )  using ()
 open Setoid B   renaming ( _≈_ to _≈₂_ ; refl to refl₂ )     using ( reflexive )
                 renaming ( sym to sym₂ ; trans to trans₂ ; Carrier to ∣B∣)
 open Func       renaming ( to to _⟨$⟩_ )                       using ( cong )
 open IsHom

 HomImageOf[_] : hom 𝑨 𝑩 → Algebra (α ⊔ β ⊔ ρᵇ) ρᵇ
 HomImageOf[ h ] =
  record { Domain = Ran ∣ h ∣ ; Interp = record { to = f' ; cong = cong' } }
   where
   open Setoid(⟨ 𝑆 ⟩ (Ran ∣ h ∣))
    using() renaming (Carrier to SRanh ; _≈_ to _≈₃_ ; refl to refl₃ )

   hhom :  ∀ {𝑓}(x : ∥ 𝑆 ∥ 𝑓 → ∣ h ∣ range )
    →      (∣ h ∣ ⟨$⟩ (𝑓 ̂ 𝑨) ((∣ h ∣ preimage) ∘ x)) ≈₂ (𝑓 ̂ 𝑩) ((∣ h ∣ image) ∘ x)

   hhom {𝑓} x = trans₂ (compatible ∥ h ∥) (cong InterpB (≡.refl , (∣ h ∣ preimage≈image) ∘ x))

   f' : SRanh → ∣ h ∣ range
   f' (𝑓 , x) =  (𝑓 ̂ 𝑩)((∣ h ∣ image)∘ x)        -- b : the image in ∣B∣
                 , (𝑓 ̂ 𝑨)((∣ h ∣ preimage) ∘ x)  -- a : the preimage in ∣A∣
                 , hhom x                        -- p : proof that `(∣ h ∣ ⟨$⟩ a) ≈₂ b`

   cong' : ∀ {x y} → x ≈₃ y → ((∣ h ∣ image) (f' x)) ≈₂ ((∣ h ∣ image) (f' y))
   cong' {(𝑓 , u)} {(.𝑓 , v)} (≡.refl , EqA) = Goal
    where
    -- Alternative formulation of the goal:
    goal : (𝑓 ̂ 𝑩)(λ i → ((∣ h ∣ image)(u i))) ≈₂ (𝑓 ̂ 𝑩)(λ i → ((∣ h ∣ image) (v i)))
    goal = cong InterpB (≡.refl , EqA )

    Goal : (∣ h ∣ image) (f' (𝑓 , u)) ≈₂ (∣ h ∣ image) (f' (𝑓 , v))
    Goal = goal
    -- Note: `EqA : ∀ i → (∣ h ∣ image) (u i) ≈₂ (∣ h ∣ image) (v i)`
```


#### <a id="homomorphic-images-of-classes-of-setoid-algebras">Homomorphic images of classes of setoid algebras</a>

Given a class `𝒦` of `𝑆`-algebras, we need a type that expresses the assertion that a given algebra is a homomorphic image of some algebra in the class, as well as a type that represents all such homomorphic images.


```agda


IsHomImageOfClass : {𝒦 : Pred (Algebra α ρᵃ)(suc α)} → Algebra α ρᵃ → Type (ov (α ⊔ ρᵃ))
IsHomImageOfClass {𝒦 = 𝒦} 𝑩 = Σ[ 𝑨 ∈ Algebra _ _ ] ((𝑨 ∈ 𝒦) ∧ (𝑩 IsHomImageOf 𝑨))

HomImageOfClass : Pred (Algebra α ρᵃ) (suc α) → Type (ov (α ⊔ ρᵃ))
HomImageOfClass 𝒦 = Σ[ 𝑩 ∈ Algebra _ _ ] IsHomImageOfClass {𝒦 = 𝒦} 𝑩
```


#### <a id="lifting-tools">Lifting tools</a>

Here are some tools that have been useful (e.g., in the road to the proof of Birkhoff's HSP theorem). The first states and proves the simple fact that the lift of an epimorphism is an epimorphism.


```agda


module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} where
 open Algebra 𝑨  using ()               renaming ( Domain to A )
 open Algebra 𝑩  using ()               renaming ( Domain to B )
 open Setoid B   using ( sym ; trans )  renaming ( _≈_ to _≈₂_ )
 open Func       using ( cong )         renaming ( to to _⟨$⟩_ )
 open Level      using ( lift ; lower )

 Lift-epi-is-epiˡ :  (h : hom 𝑨 𝑩)(ℓᵃ ℓᵇ : Level)
  →                  IsSurjective ∣ h ∣ → IsSurjective ∣ Lift-homˡ {𝑨 = 𝑨}{𝑩} h ℓᵃ ℓᵇ ∣

 Lift-epi-is-epiˡ h ℓᵃ ℓᵇ hepi {b} = Goal
  where
  open Algebra (Lift-Algˡ 𝑩 ℓᵇ) using () renaming (Domain to lB )
  open Setoid lB using () renaming ( _≈_ to _≈ₗ₂_ )

  a : 𝕌[ 𝑨 ]
  a = Inv ∣ h ∣ hepi

  lem1 : b ≈ₗ₂ (lift (lower b))
  lem1 = lift∼lower {𝑨 = B} b

  lem2' : (lower b) ≈₂ (∣ h ∣ ⟨$⟩ a)
  lem2' = sym  (InvIsInverseʳ hepi)

  lem2 : (lift (lower b)) ≈ₗ₂ (lift (∣ h ∣ ⟨$⟩ a))
  lem2 = cong{From = B} ∣ ToLiftˡ{𝑨 = 𝑩}{ℓᵇ} ∣ lem2'

  lem3 : (lift (∣ h ∣ ⟨$⟩ a)) ≈ₗ₂ ((∣ Lift-homˡ h ℓᵃ ℓᵇ ∣ ⟨$⟩ lift a))
  lem3 = lift-hom-lemma h a ℓᵃ ℓᵇ

  η : b ≈ₗ₂ (∣ Lift-homˡ h ℓᵃ ℓᵇ ∣ ⟨$⟩ lift a)
  η = trans lem1 (trans lem2 lem3)

  Goal : Image ∣ Lift-homˡ h ℓᵃ ℓᵇ ∣ ∋ b
  Goal = Image_∋_.eq (lift a) η


 Lift-Alg-hom-imageˡ :  (ℓᵃ ℓᵇ : Level) → 𝑩 IsHomImageOf 𝑨
  →                     (Lift-Algˡ 𝑩 ℓᵇ) IsHomImageOf (Lift-Algˡ 𝑨 ℓᵃ)

 Lift-Alg-hom-imageˡ ℓᵃ ℓᵇ ((φ , φhom) , φepic) = Goal
  where
  lφ : hom (Lift-Algˡ 𝑨 ℓᵃ) (Lift-Algˡ 𝑩 ℓᵇ)
  lφ = Lift-homˡ {𝑨 = 𝑨}{𝑩} (φ , φhom) ℓᵃ ℓᵇ

  lφepic : IsSurjective ∣ lφ ∣
  lφepic = Lift-epi-is-epiˡ (φ , φhom) ℓᵃ ℓᵇ φepic
  Goal : (Lift-Algˡ 𝑩 ℓᵇ) IsHomImageOf (Lift-Algˡ 𝑨 ℓᵃ)
  Goal = lφ , lφepic


module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} where
 open _≅_
 Lift-HomImage-lemma : ∀{γ} → (Lift-Alg 𝑨 γ γ) IsHomImageOf 𝑩 → 𝑨 IsHomImageOf 𝑩
 Lift-HomImage-lemma {γ} φ =  ⊙-hom ∣ φ ∣ (from Lift-≅) ,
                              ⊙-IsSurjective ∥ φ ∥ (fromIsSurjective (Lift-≅{𝑨 = 𝑨}))

module _ {𝑨 𝑨' : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} where
 open _≅_
 HomImage-≅ : 𝑨 IsHomImageOf 𝑨' → 𝑨 ≅ 𝑩 → 𝑩 IsHomImageOf 𝑨'
 HomImage-≅ φ A≅B = ⊙-hom ∣ φ ∣ (to A≅B) , ⊙-IsSurjective ∥ φ ∥ (toIsSurjective A≅B)

 HomImage-≅' : 𝑨 IsHomImageOf 𝑨' → 𝑨' ≅ 𝑩 → 𝑨 IsHomImageOf 𝑩
 HomImage-≅' φ A'≅B = (⊙-hom (from A'≅B) ∣ φ ∣) , ⊙-IsSurjective (fromIsSurjective A'≅B) ∥ φ ∥
```


--------------------------------------

<span style="float:left;">[← Setoid.Homomorphisms.Isomorphisms](Setoid.Homomorphisms.Isomorphisms.html)</span>
<span style="float:right;">[Setoid.Terms →](Setoid.Terms.html)</span>

{% include UALib.Links.md %}
