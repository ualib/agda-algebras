---
layout: default
title : Homomorphisms.Setoid.HomomorphicImages module (The Agda Universal Algebra Library)
date : 2021-08-16
author: [agda-algebras development team][]
---

### <a id="homomorphic-images">Homomorphic Images</a>

This is the [Homomorphisms.HomomorphicImages][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using (𝓞 ; 𝓥 ; Signature )

module Homomorphisms.Setoid.HomomorphicImages {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ------------------------------------------
open import Agda.Primitive        using ( _⊔_ ; lsuc ) renaming ( Set to Type )
open import Data.Product          using ( _,_ ; Σ-syntax ; _×_ )
open import Level                 using ( Level ; Lift )
open import Relation.Unary        using ( Pred ; _∈_ )
open import Relation.Binary.PropositionalEquality
                                  using ( sym ; cong-app ; _≡_ ; module ≡-Reasoning ; cong )


-- Imports from the Agda Universal Algebra Library ---------------------------------------------
open import Overture.Preliminaries             using ( ∣_∣ ; ∥_∥ ; lower∼lift ; lift∼lower )
open import Overture.Inverses                  using ( IsSurjective ; Image_∋_ ; Inv ; InvIsInv ; eq )
open import Algebras.Setoid.Basic      {𝑆 = 𝑆} using ( SetoidAlgebra ; 𝕌[_] ; Level-of-Carrier )
                                               renaming (Lift-SetoidAlg to Lift-Alg)
open import Homomorphisms.Setoid.Basic {𝑆 = 𝑆} using ( hom ; Lift-hom )

private variable
 α β ρ ρᵃ ρᵇ : Level

ov : Level → Level
ov α = 𝓞 ⊔ 𝓥 ⊔ lsuc α

\end{code}


#### <a id="hom-images-of-a-single-algebra">Hom images of a single algebra</a>

We begin with what seems, for our purposes, the most useful way to represent the class of *homomorphic images* of an algebra in dependent type theory.

\begin{code}

_IsHomImageOf_ : (𝑩 : SetoidAlgebra β ρᵇ)(𝑨 : SetoidAlgebra α ρᵃ) → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
𝑩 IsHomImageOf 𝑨 = Σ[ φ ∈ hom 𝑨 𝑩 ] IsSurjective ∣ φ ∣

HomImages : {α β ρᵇ : Level} → SetoidAlgebra α ρ → Type (α ⊔ ov (β ⊔ ρᵇ))
HomImages {α = α}{β}{ρᵇ} 𝑨 = Σ[ 𝑩 ∈ SetoidAlgebra β ρᵇ ] 𝑩 IsHomImageOf 𝑨

\end{code}

These types should be self-explanatory, but just to be sure, let's describe the Sigma type appearing in the second definition. Given an `𝑆`-algebra `𝑨 : SetoidAlgebra α ρ`, the type `HomImages 𝑨` denotes the class of algebras `𝑩 : SetoidAlgebra β ρ` with a map `φ : ∣ 𝑨 ∣ → ∣ 𝑩 ∣` such that `φ` is a surjective homomorphism.



#### <a id="hom-images-of-a-class-of-algebras">Hom images of a class of algebras</a>

Given a class `𝒦` of `𝑆`-algebras, we need a type that expresses the assertion that a given algebra is a homomorphic image of some algebra in the class, as well as a type that represents all such homomorphic images.

\begin{code}

IsHomImageOfClass : {𝒦 : Pred (SetoidAlgebra α ρ)(lsuc α)} → SetoidAlgebra α ρ → Type (ov (α ⊔ ρ))
IsHomImageOfClass {𝒦 = 𝒦} 𝑩 = Σ[ 𝑨 ∈ SetoidAlgebra _ _ ] ((𝑨 ∈ 𝒦) × (𝑩 IsHomImageOf 𝑨))

HomImageOfClass : Pred (SetoidAlgebra α ρ) (lsuc α) → Type (ov (α ⊔ ρ))
HomImageOfClass 𝒦 = Σ[ 𝑩 ∈ SetoidAlgebra _ _ ] IsHomImageOfClass {𝒦 = 𝒦} 𝑩

\end{code}



#### <a id="lifting-tools">Lifting tools</a>

Here are some tools that have been useful (e.g., in the road to the proof of Birkhoff's HSP theorem). The first states and proves the simple fact that the lift of an epimorphism is an epimorphism.

\begin{code}

module _ {𝑨 : SetoidAlgebra α ρᵃ} {𝑩 : SetoidAlgebra β ρᵇ} where
 open Level
 open ≡-Reasoning

 Lift-epi-is-epi : (h : hom 𝑨 𝑩)(ℓᵃ ℓᵇ : Level)
  →                IsSurjective ∣ h ∣ → IsSurjective ∣ Lift-hom {𝑨 = 𝑨}{𝑩} h ℓᵃ ℓᵇ ∣

 Lift-epi-is-epi h ℓᵃ ℓᵇ hepi y = eq (lift a) η
  where
   lh : hom (Lift-Alg 𝑨 ℓᵃ) (Lift-Alg 𝑩 ℓᵇ)
   lh = Lift-hom {𝑨 = 𝑨}{𝑩} h ℓᵃ ℓᵇ

   ζ : Image ∣ h ∣ ∋ (lower y)
   ζ = hepi (lower y)

   a : 𝕌[ 𝑨 ]
   a = Inv ∣ h ∣ ζ

   ν : lift (∣ h ∣ a) ≡ ∣ Lift-hom {𝑨 = 𝑨}{𝑩} h ℓᵃ ℓᵇ ∣ (Level.lift a)
   ν = cong (λ - → lift (∣ h ∣ (- a))) (lower∼lift {Level-of-Carrier{𝑆 = 𝑆} 𝑨}{β})

   η : y ≡ ∣ lh ∣ (lift a)
   η = y               ≡⟨ (cong-app lift∼lower) y ⟩
       lift (lower y)  ≡⟨ cong lift (sym (InvIsInv ∣ h ∣ ζ)) ⟩
       lift (∣ h ∣ a)  ≡⟨ ν ⟩
       ∣ lh ∣ (lift a) ∎

 Lift-Alg-hom-image : (ℓᵃ ℓᵇ : Level) → 𝑩 IsHomImageOf 𝑨
  →                   (Lift-Alg 𝑩 ℓᵇ) IsHomImageOf (Lift-Alg 𝑨 ℓᵃ)

 Lift-Alg-hom-image ℓᵃ ℓᵇ ((φ , φhom) , φepic) = Goal
  where
  lφ : hom (Lift-Alg 𝑨 ℓᵃ) (Lift-Alg 𝑩 ℓᵇ)
  lφ = Lift-hom {𝑨 = 𝑨}{𝑩} (φ , φhom) ℓᵃ ℓᵇ

  lφepic : IsSurjective ∣ lφ ∣
  lφepic = Lift-epi-is-epi (φ , φhom) ℓᵃ ℓᵇ φepic
  Goal : (Lift-Alg 𝑩 ℓᵇ) IsHomImageOf (Lift-Alg 𝑨 ℓᵃ)
  Goal = lφ , lφepic

\end{code}

--------------------------------------

[← Homomorphisms.Setoid.Isomoprhisms](Homomorphisms.Setoid.Isomoprhisms.html)
<span style="float:right;">[Terms →](Terms.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
