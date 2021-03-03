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

open import Algebras.Signatures using (Signature; 𝓞; 𝓥)
open import MGS-Subsingleton-Theorems using (global-dfunext)

module Homomorphisms.HomomorphicImages {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext} where

open import Homomorphisms.Isomorphisms{𝑆 = 𝑆}{gfe} public

\end{code}


#### <a id="images-of-a-single-algebra">Images of a single algebra</a>

We begin with what seems, for our purposes, the most useful way to represent the class of **homomorphic images** of an algebra in dependent type theory.

\begin{code}

module _ {𝓤 𝓦 : Universe} where

 HomImage : {𝑨 : Algebra 𝓤 𝑆}(𝑩 : Algebra 𝓦 𝑆)(ϕ : hom 𝑨 𝑩) → ∣ 𝑩 ∣ → 𝓤 ⊔ 𝓦 ̇
 HomImage 𝑩 ϕ = λ b → Image ∣ ϕ ∣ ∋ b

 HomImagesOf : Algebra 𝓤 𝑆 → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ⁺ ̇
 HomImagesOf 𝑨 = Σ 𝑩 ꞉ (Algebra 𝓦 𝑆) , Σ ϕ ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) , is-homomorphism 𝑨 𝑩 ϕ × Epic ϕ

\end{code}

These types should be self-explanatory, but just to be sure, let's describe the Sigma type appearing in the second definition. Given an `𝑆`-algebra `𝑨 : Algebra 𝓤 𝑆`, the type `HomImagesOf 𝑨` denotes the class of algebras `𝑩 : Algebra 𝓦 𝑆` with a map `φ : ∣ 𝑨 ∣ → ∣ 𝑩 ∣` such that `φ` is a surjective homomorphism.

Since we take the class of homomorphic images of an algebra to be closed under isomorphism, we consider `𝑩` to be a homomorphic image of `𝑨` if there exists an algebra `𝑪` which is a homomorphic image of `𝑨` and isomorphic to `𝑩`. The following type expresses this.

\begin{code}

 _is-hom-image-of_ : (𝑩 : Algebra 𝓦 𝑆)(𝑨 : Algebra 𝓤 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ⁺ ̇
 𝑩 is-hom-image-of 𝑨 = Σ 𝑪ϕ ꞉ (HomImagesOf 𝑨) , ∣ 𝑪ϕ ∣ ≅ 𝑩

\end{code}


#### <a id="images-of-a-class-of-algebras">Images of a class of algebras</a>

Given a class `𝒦` of `𝑆`-algebras, we need a type that expresses the assertion that a given algebra is a homomorphic image of some algebra in the class, as well as a type that represents all such homomorphic images.

\begin{code}

module _ {𝓤 : Universe} where

 _is-hom-image-of-class_ : Algebra 𝓤 𝑆 → Pred (Algebra 𝓤 𝑆)(𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
 𝑩 is-hom-image-of-class 𝓚 = Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , (𝑨 ∈ 𝓚) × (𝑩 is-hom-image-of 𝑨)

 HomImagesOfClass : Pred (Algebra 𝓤 𝑆) (𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
 HomImagesOfClass 𝓚 = Σ 𝑩 ꞉ (Algebra 𝓤 𝑆) , (𝑩 is-hom-image-of-class 𝓚)

\end{code}



#### <a id="lifting-tools">Lifting tools</a>

Here are some tools that have been useful (e.g., in the road to the proof of Birkhoff's HSP theorem).

The first states and proves the simple fact that the lift of an epimorphism is an epimorphism.

\begin{code}

open Lift

module _ {𝓧 𝓨 : Universe} where

 lift-of-alg-epic-is-epic : (𝓩 : Universe){𝓦 : Universe}
                            {𝑨 : Algebra 𝓧 𝑆}(𝑩 : Algebra 𝓨 𝑆)(h : hom 𝑨 𝑩)
                            -----------------------------------------------
  →                         Epic ∣ h ∣  →  Epic ∣ lift-alg-hom 𝓩 𝓦 𝑩 h ∣

 lift-of-alg-epic-is-epic 𝓩 {𝓦} {𝑨} 𝑩 h hepi y = eq y (lift a) η
  where
  lh : hom (lift-alg 𝑨 𝓩) (lift-alg 𝑩 𝓦)
  lh = lift-alg-hom 𝓩 𝓦 𝑩 h

  ζ : Image ∣ h ∣ ∋ (lower y)
  ζ = hepi (lower y)

  a : ∣ 𝑨 ∣
  a = Inv ∣ h ∣ ζ

  β : lift (∣ h ∣ a) ≡ (lift ∘ ∣ h ∣ ∘ lower{𝓦}) (lift a)
  β = ap (λ - → lift (∣ h ∣ ( - a))) (lower∼lift {𝓦} )

  η : y ≡ ∣ lh ∣ (lift a)
  η = y               ≡⟨ (extfun lift∼lower) y ⟩
      lift (lower y)  ≡⟨ ap lift (InvIsInv ∣ h ∣ ζ)⁻¹ ⟩
      lift (∣ h ∣ a)  ≡⟨ β ⟩
      ∣ lh ∣ (lift a) ∎


 lift-alg-hom-image : {𝓩 𝓦 : Universe}
                      {𝑨 : Algebra 𝓧 𝑆}{𝑩 : Algebra 𝓨 𝑆}
  →                   𝑩 is-hom-image-of 𝑨
                      -----------------------------------------------
  →                   (lift-alg 𝑩 𝓦) is-hom-image-of (lift-alg 𝑨 𝓩)

 lift-alg-hom-image {𝓩}{𝓦}{𝑨}{𝑩} ((𝑪 , ϕ , ϕhom , ϕepic) , C≅B) =
  (lift-alg 𝑪 𝓦 , ∣ lϕ ∣ , ∥ lϕ ∥ , lϕepic) , lift-alg-iso C≅B
   where
   lϕ : hom (lift-alg 𝑨 𝓩) (lift-alg 𝑪 𝓦)
   lϕ = (lift-alg-hom 𝓩 𝓦 𝑪) (ϕ , ϕhom)

   lϕepic : Epic ∣ lϕ ∣
   lϕepic = lift-of-alg-epic-is-epic 𝓩 𝑪 (ϕ , ϕhom) ϕepic

\end{code}

------

#### Deprecated functions

The functions below will be removed from the future releases of the [UALib][] as they don't seem to be especially useful.

\begin{code}

lift-function : {𝓧 : Universe}{𝓨 : Universe}{𝓩 : Universe}{𝓦 : Universe}
                (A : 𝓧 ̇)(B : 𝓨 ̇) → (f : A → B)
                ---------------------------------
 →              Lift{𝓩} A → Lift{𝓦} B

lift-function  A B f = λ la → lift (f (lower la))

\end{code}

--------------------------------------

[← Homomorphisms.Isomorphisms](Homomorphisms.Isomorphisms.html)
<span style="float:right;">[Terms →](Terms.html)</span>

{% include UALib.Links.md %}
