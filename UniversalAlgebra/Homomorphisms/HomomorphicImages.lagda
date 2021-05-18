---
layout: default
title : Homomorphisms.HomomorphicImages module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="homomorphic-images">Homomorphic Images</a>

This section describes the [Homomorphisms.HomomorphicImages][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

-- Imports from Agda (builtin/primitive) and the Agda Standard Library
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_,_; Σ; _×_)
open import Level renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality.Core using (cong; cong-app; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Unary using (Pred; ∅; _∪_; _∈_; _⊆_)

-- Imports from the Agda Universal Algebra Library
open import Algebras.Basic
open import Overture.Preliminaries
 using (Type; 𝓞; 𝓤; 𝓥; 𝓦; 𝓧; 𝓨; Π; -Π; -Σ; _⁻¹; 𝑖𝑑; ∣_∣; ∥_∥; lower∼lift; lift∼lower)
open import Overture.Inverses using (IsSurjective; Image_∋_; Inv; InvIsInv; eq)



module Homomorphisms.HomomorphicImages {𝑆 : Signature 𝓞 𝓥} where

open import Algebras.Products{𝑆 = 𝑆} using (ov)
open import Homomorphisms.Basic {𝑆 = 𝑆} using (hom; 𝓁𝒾𝒻𝓉; 𝓁ℴ𝓌ℯ𝓇)
open import Homomorphisms.Isomorphisms {𝑆 = 𝑆} using (Lift-hom)


\end{code}


#### <a id="images-of-a-single-algebra">Images of a single algebra</a>

We begin with what seems, for our purposes, the most useful way to represent the class of *homomorphic images* of an algebra in dependent type theory.

\begin{code}

IsHomImage : {𝑨 : Algebra 𝓤 𝑆}(𝑩 : Algebra 𝓦 𝑆) → Type(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦)
IsHomImage {𝑨 = 𝑨} 𝑩 = Σ[ φ ꞉ hom 𝑨 𝑩 ] IsSurjective ∣ φ ∣ -- λ b → Image ∣ ϕ ∣ ∋ b

HomImages : Algebra 𝓤 𝑆 → Type(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ lsuc 𝓦)
HomImages {𝓦 = 𝓦}𝑨 = Σ[ 𝑩 ꞉ Algebra 𝓦 𝑆 ] IsHomImage{𝑨 = 𝑨} 𝑩

\end{code}

These types should be self-explanatory, but just to be sure, let's describe the Sigma type appearing in the second definition. Given an `𝑆`-algebra `𝑨 : Algebra 𝓤 𝑆`, the type `HomImages 𝑨` denotes the class of algebras `𝑩 : Algebra 𝓦 𝑆` with a map `φ : ∣ 𝑨 ∣ → ∣ 𝑩 ∣` such that `φ` is a surjective homomorphism.



#### <a id="images-of-a-class-of-algebras">Images of a class of algebras</a>

Given a class `𝒦` of `𝑆`-algebras, we need a type that expresses the assertion that a given algebra is a homomorphic image of some algebra in the class, as well as a type that represents all such homomorphic images.

\begin{code}

module _ {𝓤 : Level} where

 IsHomImageOfClass : {𝒦 : Pred (Algebra 𝓤 𝑆)(lsuc 𝓤)} → Algebra 𝓤 𝑆 → Type(ov 𝓤)
 IsHomImageOfClass {𝒦 = 𝒦} 𝑩 = Σ[ 𝑨 ꞉ Algebra 𝓤 𝑆 ] ((𝑨 ∈ 𝒦) × (IsHomImage {𝑨 = 𝑨} 𝑩))

 HomImageOfClass : Pred (Algebra 𝓤 𝑆) (lsuc 𝓤) → Type(ov 𝓤)
 HomImageOfClass 𝒦 = Σ[ 𝑩 ꞉ Algebra 𝓤 𝑆 ] IsHomImageOfClass{𝒦} 𝑩

\end{code}



#### <a id="lifting-tools">Lifting tools</a>

Here are some tools that have been useful (e.g., in the road to the proof of Birkhoff's HSP theorem). The first states and proves the simple fact that the lift of an epimorphism is an epimorphism.

\begin{code}

open Lift
Lift-epi-is-epi : {𝓩 𝓦 : Level}{𝑨 : Algebra 𝓧 𝑆}
                  (𝑩 : Algebra 𝓨 𝑆)(h : hom 𝑨 𝑩)
                  ----------------------------------------------------------
 →                IsSurjective ∣ h ∣ → IsSurjective ∣ Lift-hom 𝓩 𝓦 𝑩 h ∣

Lift-epi-is-epi {𝓩 = 𝓩} {𝓦} {𝑨} 𝑩 h hepi y = eq (lift a) η
  where
   lh : hom (Lift-alg 𝑨 𝓩) (Lift-alg 𝑩 𝓦)
   lh = Lift-hom 𝓩 𝓦 𝑩 h

   ζ : Image ∣ h ∣ ∋ (lower y)
   ζ = hepi (lower y)

   a : ∣ 𝑨 ∣
   a = Inv ∣ h ∣ ζ

   β : lift (∣ h ∣ a) ≡ ∣ Lift-hom 𝓩 𝓦 𝑩 h ∣ (lift a)
   β = cong (λ - → lift (∣ h ∣ (- a))) (lower∼lift {level-of-alg 𝑨}{𝓦})

   η : y ≡ ∣ lh ∣ (lift a)
   η = y               ≡⟨ (cong-app lift∼lower) y ⟩
       lift (lower y)  ≡⟨ cong lift (InvIsInv ∣ h ∣ ζ)⁻¹ ⟩
       lift (∣ h ∣ a)  ≡⟨ β ⟩
       ∣ lh ∣ (lift a) ∎


Lift-alg-hom-image : {𝓩 𝓦 : Level}{𝑨 : Algebra 𝓧 𝑆}{𝑩 : Algebra 𝓨 𝑆}
 →                   IsHomImage {𝑨 = 𝑨} 𝑩
 →                   IsHomImage {𝑨 = Lift-alg 𝑨 𝓩} (Lift-alg 𝑩 𝓦)

Lift-alg-hom-image {𝓩 = 𝓩}{𝓦}{𝑨}{𝑩} ((φ , φhom) , φepic) = γ
 where
  lφ : hom (Lift-alg 𝑨 𝓩) (Lift-alg 𝑩 𝓦)
  lφ = (Lift-hom 𝓩 𝓦 𝑩) (φ , φhom)

  lφepic : IsSurjective ∣ lφ ∣
  lφepic = Lift-epi-is-epi {𝓩 = 𝓩} 𝑩 (φ , φhom) φepic
  γ : IsHomImage (Lift-alg 𝑩 𝓦)
  γ = lφ , lφepic

\end{code}

--------------------------------------

[← Homomorphisms.Isomorphisms](Homomorphisms.Isomorphisms.html)
<span style="float:right;">[Terms →](Terms.html)</span>

{% include UALib.Links.md %}
