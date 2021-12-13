---
layout: default
title : "Base.Homomorphisms.Properties module (The Agda Universal Algebra Library)"
date : "2021-09-08"
author: "agda-algebras development team"
---

### <a id="properties-of-homomorphisms">Properties of Homomorphisms</a>

This is the [Base.Homomorphisms.Properties] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Base.Algebras.Basic

module Base.Homomorphisms.Properties {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library --------------------------------
open import Data.Product   using ( _,_ )
open import Function.Base  using ( _∘_ )
open import Level          using ( Level )
open import Relation.Binary.PropositionalEquality
                           using ( _≡_ ; module ≡-Reasoning ; cong ; refl )

-- -- Imports from the Agda Universal Algebras Library --------------------------------
open import Base.Overture.Preliminaries       using ( ∣_∣ ; ∥_∥ )
open import Base.Homomorphisms.Basic  {𝑆 = 𝑆} using ( hom ; is-homomorphism )
private variable α β γ ρ : Level

\end{code}


#### <a id="homomorphism-composition">Homomorphism composition</a>

The composition of homomorphisms is again a homomorphism.  We formalize this in a number of alternative ways.

\begin{code}

open ≡-Reasoning

module _ (𝑨 : Algebra α 𝑆){𝑩 : Algebra β 𝑆}(𝑪 : Algebra γ 𝑆) where

  ∘-hom : hom 𝑨 𝑩  →  hom 𝑩 𝑪  →  hom 𝑨 𝑪
  ∘-hom (g , ghom) (h , hhom) = h ∘ g , Goal where

   Goal : ∀ 𝑓 a → (h ∘ g)((𝑓 ̂ 𝑨) a) ≡ (𝑓 ̂ 𝑪)(h ∘ g ∘ a)
   Goal 𝑓 a = (h ∘ g)((𝑓 ̂ 𝑨) a)     ≡⟨ cong h ( ghom 𝑓 a ) ⟩
              h ((𝑓 ̂ 𝑩)(g ∘ a))     ≡⟨ hhom 𝑓 ( g ∘ a ) ⟩
              (𝑓 ̂ 𝑪)(h ∘ g ∘ a)     ∎


  ∘-is-hom : {f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣}{g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣}
   →         is-homomorphism 𝑨 𝑩 f → is-homomorphism 𝑩 𝑪 g → is-homomorphism 𝑨 𝑪 (g ∘ f)
  ∘-is-hom {f} {g} fhom ghom = ∥ ∘-hom (f , fhom) (g , ghom) ∥

\end{code}

A homomorphism from `𝑨` to `𝑩` can be lifted to a homomorphism from `Lift-Alg 𝑨 ℓᵃ` to `Lift-Alg 𝑩 ℓᵇ`.

\begin{code}

open Level

Lift-hom : {𝑨 : Algebra α 𝑆}(ℓᵃ : Level){𝑩 : Algebra β 𝑆} (ℓᵇ : Level)
 →         hom 𝑨 𝑩  →  hom (Lift-Alg 𝑨 ℓᵃ) (Lift-Alg 𝑩 ℓᵇ)

Lift-hom {𝑨 = 𝑨} ℓᵃ {𝑩} ℓᵇ (f , fhom) = lift ∘ f ∘ lower , Goal
 where
 lABh : is-homomorphism (Lift-Alg 𝑨 ℓᵃ) 𝑩 (f ∘ lower)
 lABh = ∘-is-hom (Lift-Alg 𝑨 ℓᵃ) 𝑩 {lower}{f} (λ _ _ → refl) fhom

 Goal : is-homomorphism(Lift-Alg 𝑨 ℓᵃ)(Lift-Alg 𝑩 ℓᵇ) (lift ∘ (f ∘ lower))
 Goal = ∘-is-hom (Lift-Alg 𝑨 ℓᵃ) (Lift-Alg 𝑩 ℓᵇ){f ∘ lower}{lift} lABh λ _ _ → refl

\end{code}

We should probably point out that while the lifting and lowering homomorphisms are important for our formal treatment of algebras in type theory, they never arise---in fact, they are not even definable---in classical universal algebra based on set theory.

---------------------------------

<span style="float:left;">[← Base.Homomorphisms.Basic](Base.Homomorphisms.Basic.html)</span>
<span style="float:right;">[Base.Homomorphisms.Kernels →](Base.Homomorphisms.Kernels.html)</span>

{% include UALib.Links.md %}
