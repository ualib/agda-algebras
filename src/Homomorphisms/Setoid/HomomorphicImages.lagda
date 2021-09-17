---
layout: default
title : "Homomorphisms.Setoid.HomomorphicImages module (The Agda Universal Algebra Library)"
date : "2021-08-16"
author: "agda-algebras development team"
---

#### <a id="homomorphic-images-of-setoid-algebras">Homomorphic images of setoid algebras</a>

This is the [Homomorphisms.HomomorphicImages][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using (𝓞 ; 𝓥 ; Signature )

module Homomorphisms.Setoid.HomomorphicImages {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ------------------------------------------
open import Agda.Primitive        using ( _⊔_ ; lsuc ) renaming ( Set to Type )
open import Data.Product          using ( _,_ ; Σ-syntax ; _×_ )
open import Function.Equality     using ( Π ; _⟶_ )
open import Level                 using ( Level ; Lift )
open import Relation.Binary       using ( Setoid )
open import Relation.Unary        using ( Pred ; _∈_ )
open import Relation.Binary.PropositionalEquality as PE
                                  using ( cong-app ; _≡_ ; module ≡-Reasoning )


-- Imports from the Agda Universal Algebra Library ---------------------------------------------
open import Overture.Preliminaries                  using ( ∣_∣ ; ∥_∥ )
open import Overture.Setoid.Preliminaries           using ( lower∼lift ; lift∼lower ; slift )
open import Overture.Setoid.Inverses as OSI         using ( Image_∋_ ; Inv ; InvIsInv ; eq )
open import Overture.Setoid.Surjective              using ( IsSurjective )
open import Algebras.Setoid.Basic           {𝑆 = 𝑆} using ( SetoidAlgebra ; 𝕌[_] ; Level-of-Carrier
                                                          ; Lift-Alg ; ov )
open import Homomorphisms.Setoid.Basic      {𝑆 = 𝑆} using ( hom )
open import Homomorphisms.Setoid.Properties {𝑆 = 𝑆} using ( Lift-hom ; lift-hom-lemma )

private variable
 α β ρ ρᵃ ρᵇ : Level

\end{code}

We begin with what seems, for our purposes, the most useful way to represent the class of *homomorphic images* of an algebra in dependent type theory.

\begin{code}

_IsHomImageOf_ : (𝑩 : SetoidAlgebra β ρᵇ)(𝑨 : SetoidAlgebra α ρᵃ) → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β ⊔ ρᵃ ⊔ ρᵇ)
𝑩 IsHomImageOf 𝑨 = Σ[ φ ∈ hom 𝑨 𝑩 ] IsSurjective ∣ φ ∣

HomImages : {α β ρᵇ : Level} → SetoidAlgebra α ρ → Type (α ⊔ ρ ⊔ ov (β ⊔ ρᵇ))
HomImages {α = α}{β}{ρᵇ} 𝑨 = Σ[ 𝑩 ∈ SetoidAlgebra β ρᵇ ] 𝑩 IsHomImageOf 𝑨

\end{code}

These types should be self-explanatory, but just to be sure, let's describe the Sigma type appearing in the second definition. Given an `𝑆`-algebra `𝑨 : SetoidAlgebra α ρ`, the type `HomImages 𝑨` denotes the class of algebras `𝑩 : SetoidAlgebra β ρ` with a map `φ : ∣ 𝑨 ∣ → ∣ 𝑩 ∣` such that `φ` is a surjective homomorphism.



#### <a id="homomorphic-images-of-classes-of-setoid-algebras">Homomorphic images of classes of setoid algebras</a>

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
 open SetoidAlgebra
 open Setoid
 open Π

 Lift-epi-is-epi : (h : hom 𝑨 𝑩)(ℓᵃ ℓᵇ : Level)
  →                IsSurjective ∣ h ∣ → IsSurjective ∣ Lift-hom {𝑨 = 𝑨}{𝑩} h ℓᵃ ℓᵇ ∣

 Lift-epi-is-epi h ℓᵃ ℓᵇ hepi b = Goal -- eq (lift a) η
  where
  A = Domain (Lift-Alg 𝑨 ℓᵃ)
  B = Domain (Lift-Alg 𝑩 ℓᵇ)
  _≈B≈_ = (_≈_ B)

  ζ : Image ∣ h ∣ ∋ (lower b)
  ζ = hepi (lower b)

  a : 𝕌[ 𝑨 ]
  a = Inv ∣ h ∣ ζ

  lem1 : b ≈B≈ lift (lower b)
  lem1 = lift∼lower {𝑨 = Domain 𝑩} b
  lem2' : (_≈_ (Domain 𝑩)) (lower b) (∣ h ∣ ⟨$⟩ a)
  lem2' = sym (Domain 𝑩) (InvIsInv ∣ h ∣ ζ)
  lem2 : lift (lower b) ≈B≈ lift (∣ h ∣ ⟨$⟩ a)
  lem2 = cong{From = Domain 𝑩} (slift{ℓ = ℓᵇ}) lem2'
  lem3 : lift (∣ h ∣ ⟨$⟩ a) ≈B≈ (∣ Lift-hom h ℓᵃ ℓᵇ ∣ ⟨$⟩ lift a)
  lem3 = lift-hom-lemma h a ℓᵃ ℓᵇ
  η : b ≈B≈ (∣ Lift-hom h ℓᵃ ℓᵇ ∣ ⟨$⟩ lift a)
  η = trans B lem1 (trans B lem2 lem3)
  Goal : Image ∣ Lift-hom h ℓᵃ ℓᵇ ∣ ∋ b
  Goal = eq (lift a) η


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

<span style="float:left;">[← Homomorphisms.Setoid.Isomoprhisms](Homomorphisms.Setoid.Isomoprhisms.html)</span>
<span style="float:right;">[Terms →](Terms.html)</span>

{% include UALib.Links.md %}
