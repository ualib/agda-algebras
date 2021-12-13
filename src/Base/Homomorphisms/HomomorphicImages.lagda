---
layout: default
title : "Base.Homomorphisms.HomomorphicImages module (The Agda Universal Algebra Library)"
date : "2021-01-14"
author: "agda-algebras development team"
---

### <a id="homomorphic-images">Homomorphic Images</a>

This is the [Base.Homomorphisms.HomomorphicImages][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Base.Algebras.Basic

module Base.Homomorphisms.HomomorphicImages {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ------------------------------------------
open import Agda.Primitive using ( _⊔_ ; lsuc ) renaming ( Set to Type )
open import Data.Product   using ( _,_ ; Σ-syntax ; Σ ; _×_ )
open import Level          using ( Level )
open import Relation.Binary.PropositionalEquality
                           using ( _≡_ ; module ≡-Reasoning ; cong ; cong-app ; sym )
open import Relation.Unary using ( Pred ; _∈_ )

-- Imports from the Agda Universal Algebra Library ------------------------------------------
open import Base.Overture.Preliminaries      using ( 𝑖𝑑 ; ∣_∣ ; ∥_∥ ; lower∼lift ; lift∼lower )
open import Base.Overture.Inverses           using ( Image_∋_ ; Inv ; InvIsInverseʳ ; eq )
open import Base.Overture.Surjective         using ( IsSurjective )
open import Base.Algebras.Products   {𝑆 = 𝑆} using ( ov )
open import Base.Homomorphisms.Basic {𝑆 = 𝑆} using ( hom ; 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇 )
open import Base.Homomorphisms.Properties {𝑆 = 𝑆} using ( Lift-hom )

\end{code}


#### <a id="images-of-a-single-algebra">Images of a single algebra</a>

We begin with what seems, for our purposes, the most useful way to represent the class of *homomorphic images* of an algebra in dependent type theory.

\begin{code}

module _ {α β : Level } where

 _IsHomImageOf_ : (𝑩 : Algebra β 𝑆)(𝑨 : Algebra α 𝑆) → Type _
 𝑩 IsHomImageOf 𝑨 = Σ[ φ ∈ hom 𝑨 𝑩 ] IsSurjective ∣ φ ∣

 HomImages : Algebra α 𝑆 → Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ lsuc β)
 HomImages 𝑨 = Σ[ 𝑩 ∈ Algebra β 𝑆 ] 𝑩 IsHomImageOf 𝑨

\end{code}

These types should be self-explanatory, but just to be sure, let's describe the Sigma type appearing in the second definition. Given an `𝑆`-algebra `𝑨 : Algebra α 𝑆`, the type `HomImages 𝑨` denotes the class of algebras `𝑩 : Algebra β 𝑆` with a map `φ : ∣ 𝑨 ∣ → ∣ 𝑩 ∣` such that `φ` is a surjective homomorphism.


#### <a id="images-of-a-class-of-algebras">Images of a class of algebras</a>

Given a class `𝒦` of `𝑆`-algebras, we need a type that expresses the assertion that a given algebra is a homomorphic image of some algebra in the class, as well as a type that represents all such homomorphic images.

\begin{code}

module _ {α : Level} where

 IsHomImageOfClass : {𝒦 : Pred (Algebra α 𝑆)(lsuc α)} → Algebra α 𝑆 → Type(ov α)
 IsHomImageOfClass {𝒦 = 𝒦} 𝑩 = Σ[ 𝑨 ∈ Algebra α 𝑆 ] ((𝑨 ∈ 𝒦) × (𝑩 IsHomImageOf 𝑨))

 HomImageOfClass : Pred (Algebra α 𝑆) (lsuc α) → Type(ov α)
 HomImageOfClass 𝒦 = Σ[ 𝑩 ∈ Algebra α 𝑆 ] IsHomImageOfClass{𝒦} 𝑩

\end{code}


#### <a id="lifting-tools">Lifting tools</a>

Here are some tools that have been useful (e.g., in the road to the proof of Birkhoff's HSP theorem). The first states and proves the simple fact that the lift of an epimorphism is an epimorphism.

\begin{code}

module _ {α β : Level} where

 open Level
 open ≡-Reasoning

 Lift-epi-is-epi : {𝑨 : Algebra α 𝑆}(ℓᵃ : Level){𝑩 : Algebra β 𝑆}(ℓᵇ : Level)(h : hom 𝑨 𝑩)
  →                IsSurjective ∣ h ∣ → IsSurjective ∣ Lift-hom ℓᵃ {𝑩} ℓᵇ h ∣

 Lift-epi-is-epi {𝑨 = 𝑨} ℓᵃ {𝑩} ℓᵇ h hepi y = eq (lift a) η
  where
   lh : hom (Lift-Alg 𝑨 ℓᵃ) (Lift-Alg 𝑩 ℓᵇ)
   lh = Lift-hom ℓᵃ {𝑩} ℓᵇ h

   ζ : Image ∣ h ∣ ∋ (lower y)
   ζ = hepi (lower y)

   a : ∣ 𝑨 ∣
   a = Inv ∣ h ∣ ζ

   ν : lift (∣ h ∣ a) ≡ ∣ Lift-hom ℓᵃ {𝑩} ℓᵇ h ∣ (Level.lift a)
   ν = cong (λ - → lift (∣ h ∣ (- a))) (lower∼lift {Level-of-Carrier 𝑨}{β})

   η : y ≡ ∣ lh ∣ (lift a)
   η = y               ≡⟨ (cong-app lift∼lower) y ⟩
       lift (lower y)  ≡⟨ cong lift (sym (InvIsInverseʳ ζ)) ⟩
       lift (∣ h ∣ a)  ≡⟨ ν ⟩
       ∣ lh ∣ (lift a) ∎

 Lift-Alg-hom-image : {𝑨 : Algebra α 𝑆}(ℓᵃ : Level){𝑩 : Algebra β 𝑆}(ℓᵇ : Level)
  →                   𝑩 IsHomImageOf 𝑨
  →                   (Lift-Alg 𝑩 ℓᵇ) IsHomImageOf (Lift-Alg 𝑨 ℓᵃ)

 Lift-Alg-hom-image {𝑨 = 𝑨} ℓᵃ {𝑩} ℓᵇ ((φ , φhom) , φepic) = Goal
  where
  lφ : hom (Lift-Alg 𝑨 ℓᵃ) (Lift-Alg 𝑩 ℓᵇ)
  lφ = Lift-hom ℓᵃ {𝑩} ℓᵇ (φ , φhom)

  lφepic : IsSurjective ∣ lφ ∣
  lφepic = Lift-epi-is-epi ℓᵃ {𝑩} ℓᵇ (φ , φhom) φepic
  Goal : (Lift-Alg 𝑩 ℓᵇ) IsHomImageOf _
  Goal = lφ , lφepic

\end{code}

--------------------------------------

<span style="float:left;">[← Base.Homomorphisms.Isomorphisms](Base.Homomorphisms.Isomorphisms.html)</span>
<span style="float:right;">[Base.Terms →](Base.Terms.html)</span>

{% include UALib.Links.md %}
