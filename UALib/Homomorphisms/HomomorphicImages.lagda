---
layout: default
title : UALib.Homomorphisms.HomomorphicImages module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="homomorphic-images">Homomorphic Images</a>

This section describes the [UALib.Homomorphisms.HomomorphicImages][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras.Signatures using (Signature; 𝓞; 𝓥)
open import UALib.Prelude.Preliminaries using (global-dfunext)

module UALib.Homomorphisms.HomomorphicImages {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext} where

open import UALib.Homomorphisms.Isomorphisms{𝑆 = 𝑆}{gfe} public

\end{code}


#### <a id="images-of-a-single-algebra">Images of a single algebra</a>

We begin with what seems to be (for our purposes at least) the most useful way to represent, in dependent type theory, the class of **homomomrphic images** of an algebra.

\begin{code}

HomImage : {𝓤 𝓦 : Universe}{𝑨 : Algebra 𝓤 𝑆}(𝑩 : Algebra 𝓦 𝑆)(ϕ : hom 𝑨 𝑩) → ∣ 𝑩 ∣ → 𝓤 ⊔ 𝓦 ̇
HomImage 𝑩 ϕ = λ b → Image ∣ ϕ ∣ ∋ b

HomImagesOf : {𝓤 𝓦 : Universe} → Algebra 𝓤 𝑆 → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ⁺ ̇
HomImagesOf {𝓤}{𝓦} 𝑨 = Σ 𝑩 ꞉ (Algebra 𝓦 𝑆) , Σ ϕ ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) ,
                                                  is-homomorphism 𝑨 𝑩 ϕ × Epic ϕ

\end{code}




#### <a id="images-of-a-class-of-algebras">Images of a class of algebras</a>

Here are a few more definitions, derived from the one above, that will come in handy.

\begin{code}

_is-hom-image-of_ : {𝓤 𝓦 : Universe} (𝑩 : Algebra 𝓦 𝑆)
  →                (𝑨 : Algebra 𝓤 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ⁺ ̇

_is-hom-image-of_ {𝓤}{𝓦} 𝑩 𝑨 = Σ 𝑪ϕ ꞉ (HomImagesOf{𝓤}{𝓦} 𝑨) , ∣ 𝑪ϕ ∣ ≅ 𝑩

_is-hom-image-of-class_ : {𝓤 : Universe} → Algebra 𝓤 𝑆 → Pred (Algebra 𝓤 𝑆)(𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
_is-hom-image-of-class_ {𝓤} 𝑩 𝓚 = Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , (𝑨 ∈ 𝓚) × (𝑩 is-hom-image-of 𝑨)

HomImagesOfClass : {𝓤 : Universe} → Pred (Algebra 𝓤 𝑆) (𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
HomImagesOfClass 𝓚 = Σ 𝑩 ꞉ (Algebra _ 𝑆) , (𝑩 is-hom-image-of-class 𝓚)

all-ops-in_and_commute-with : {𝓤 𝓦 : Universe}
                              (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆)
 →                            (∣ 𝑨 ∣  → ∣ 𝑩 ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

all-ops-in 𝑨 and 𝑩 commute-with g = is-homomorphism 𝑨 𝑩 g

\end{code}



#### <a id="lifting-tools">Lifting tools</a>

\begin{code}

open Lift

lift-function : (𝓧 : Universe){𝓨 : Universe}
                (𝓩 : Universe){𝓦 : Universe}
                (A : 𝓧 ̇)(B : 𝓨 ̇) → (f : A → B)
                ---------------------------------
 →              Lift{𝓧}{𝓩} A → Lift{𝓨}{𝓦} B

lift-function  𝓧 {𝓨} 𝓩 {𝓦} A B f = λ la → lift (f (lower la))


lift-of-alg-epic-is-epic : (𝓧 : Universe){𝓨 : Universe}
                           (𝓩 : Universe){𝓦 : Universe}
                           (𝑨 : Algebra 𝓧 𝑆)(𝑩 : Algebra 𝓨 𝑆)
                           (f : hom 𝑨 𝑩)  →  Epic ∣ f ∣
                           ------------------------------------
 →                         Epic ∣ lift-alg-hom 𝓧 𝓩{𝓦} 𝑨 𝑩 f ∣

lift-of-alg-epic-is-epic 𝓧 {𝓨} 𝓩 {𝓦} 𝑨 𝑩 f fepi y = eq y (lift a) η
 where
  lf : hom (lift-alg 𝑨 𝓩) (lift-alg 𝑩 𝓦)
  lf = lift-alg-hom 𝓧 𝓩 𝑨 𝑩 f

  b : ∣ 𝑩 ∣
  b = lower y

  ζ : Image ∣ f ∣ ∋ b
  ζ = fepi b

  a : ∣ 𝑨 ∣
  a = Inv ∣ f ∣ b ζ

  β : lift (∣ f ∣ a) ≡ (lift ∘ ∣ f ∣ ∘ lower{𝓦 = 𝓦}) (lift a)
  β = ap (λ - → lift (∣ f ∣ ( - a))) (lower∼lift{𝓦 = 𝓦})

  η : y ≡ ∣ lf ∣ (lift a)
  η = y               ≡⟨ (intensionality lift∼lower) y ⟩
      lift b          ≡⟨ ap lift (InvIsInv ∣ f ∣ (lower y) ζ)⁻¹ ⟩
      lift (∣ f ∣ a)  ≡⟨ β ⟩
      ∣ lf ∣ (lift a) ∎


lift-alg-hom-image : {𝓧 𝓨 𝓩 𝓦 : Universe}
                     {𝑨 : Algebra 𝓧 𝑆}{𝑩 : Algebra 𝓨 𝑆}
 →                   𝑩 is-hom-image-of 𝑨
                     -----------------------------------------------
 →                   (lift-alg 𝑩 𝓦) is-hom-image-of (lift-alg 𝑨 𝓩)

lift-alg-hom-image {𝓧}{𝓨}{𝓩}{𝓦}{𝑨}{𝑩} ((𝑪 , ϕ , ϕhom , ϕepic) , C≅B) =
 (lift-alg 𝑪 𝓦 , ∣ lϕ ∣ , ∥ lϕ ∥ , lϕepic) , lift-alg-iso 𝓨 𝓦 𝑪 𝑩 C≅B
  where
   lϕ : hom (lift-alg 𝑨 𝓩) (lift-alg 𝑪 𝓦)
   lϕ = (lift-alg-hom 𝓧 𝓩 𝑨 𝑪) (ϕ , ϕhom)

   lϕepic : Epic ∣ lϕ ∣
   lϕepic = lift-of-alg-epic-is-epic 𝓧 𝓩 𝑨 𝑪 (ϕ , ϕhom) ϕepic

\end{code}

--------------------------------------

[← UALib.Homomorphisms.Isomorphisms](UALib.Homomorphisms.Isomorphisms.html)
<span style="float:right;">[UALib.Terms →](UALib.Terms.html)</span>

{% include UALib.Links.md %}
