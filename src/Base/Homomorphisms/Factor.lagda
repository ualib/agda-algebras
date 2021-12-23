---
layout: default
title : "Base.Homomorphisms.Factor module (The Agda Universal Algebra Library)"
date : "2021-09-20"
author: "agda-algebras development team"
---

### <a id="homomorphism-decomposition">Homomorphism decomposition</a>

This is the [Base.Homomorphisms.Factor][] module of the [Agda Universal Algebra Library][] in which we prove the following theorem:

If `τ : hom 𝑨 𝑩`, `ν : hom 𝑨 𝑪`, `ν` is surjective, and `ker ν ⊆ ker τ`, then there exists `φ : hom 𝑪 𝑩` such that `τ = φ ∘ ν` so the following diagram commutes:

```
𝑨 --- ν ->> 𝑪
 \         .
  \       .
   τ     φ
    \   .
     \ .
      V
      𝑩
```

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Base.Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Base.Homomorphisms.Factor {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ---------------------------------------
open import Agda.Primitive using ( Level )
open import Data.Product   using ( Σ-syntax ; _,_ ) renaming (proj₁ to fst ; proj₂ to snd)
open import Function.Base  using ( _∘_ )
open import Relation.Binary.PropositionalEquality using ( module ≡-Reasoning ; _≡_ ; cong )
open import Relation.Unary using ( _⊆_ )

-- Imports from agda-algebras --------------------------------------------------------------
open import Base.Overture.Preliminaries      using ( ∣_∣ ; ∥_∥ ; _⁻¹ )
open import Base.Overture.Surjective         using ( IsSurjective ; SurjInv ; SurjInvIsInverseʳ ; epic-factor )
open import Base.Relations.Discrete          using ( kernel )
open import Base.Equality.Welldefined        using ( swelldef )
open import Base.Algebras.Basic              using ( Algebra ; _̂_)
open import Base.Homomorphisms.Basic {𝑆 = 𝑆} using ( hom ; epi )

private variable α β γ : Level

module _ {𝑨 : Algebra α 𝑆}{𝑪 : Algebra γ 𝑆} where

 open ≡-Reasoning

 HomFactor : swelldef 𝓥 γ
  →          (𝑩 : Algebra β 𝑆)(τ : hom 𝑨 𝑩)(ν : hom 𝑨 𝑪)
  →          kernel ∣ ν ∣ ⊆ kernel ∣ τ ∣ → IsSurjective ∣ ν ∣
             --------------------------------------------------
  →          Σ[ φ ∈ (hom 𝑪 𝑩)] ∀ x → ∣ τ ∣ x ≡ ∣ φ ∣ (∣ ν ∣ x)

 HomFactor wd 𝑩 τ ν Kντ νE = (φ , φIsHomCB) , τφν
  where
   νInv : ∣ 𝑪 ∣ → ∣ 𝑨 ∣
   νInv = SurjInv ∣ ν ∣ νE

   η : ∀ c → ∣ ν ∣ (νInv c) ≡ c
   η c = SurjInvIsInverseʳ ∣ ν ∣ νE c

   φ : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
   φ = ∣ τ ∣ ∘ νInv

   ξ : ∀ a → kernel ∣ ν ∣ (a , νInv (∣ ν ∣ a))
   ξ a = (η (∣ ν ∣ a))⁻¹

   τφν : ∀ x → ∣ τ ∣ x ≡ φ (∣ ν ∣ x)
   τφν = λ x → Kντ (ξ x)

   φIsHomCB : ∀ 𝑓 c → φ ((𝑓 ̂ 𝑪) c) ≡ ((𝑓 ̂ 𝑩)(φ ∘ c))
   φIsHomCB 𝑓 c =
    φ ((𝑓 ̂ 𝑪) c)                    ≡⟨ cong φ (wd (𝑓 ̂ 𝑪) c (∣ ν ∣ ∘ (νInv ∘ c)) (λ i → (η (c i))⁻¹))⟩
    φ ((𝑓 ̂ 𝑪)(∣ ν ∣ ∘(νInv ∘ c)))   ≡⟨ cong φ (∥ ν ∥ 𝑓 (νInv ∘ c))⁻¹ ⟩
    φ (∣ ν ∣((𝑓 ̂ 𝑨)(νInv ∘ c)))     ≡⟨ (τφν ((𝑓 ̂ 𝑨)(νInv ∘ c)))⁻¹ ⟩
    ∣ τ ∣((𝑓 ̂ 𝑨)(νInv ∘ c))         ≡⟨ ∥ τ ∥ 𝑓 (νInv ∘ c) ⟩
    (𝑓 ̂ 𝑩)(λ x → ∣ τ ∣(νInv (c x))) ∎

\end{code}

If, in addition to the hypotheses of the last theorem, we assume τ is epic, then so is φ. (Note that the proof also requires an additional local function extensionality postulate, `funext β β`.)

\begin{code}

 HomFactorEpi : swelldef 𝓥 γ
  →             (𝑩 : Algebra β 𝑆)(τ : hom 𝑨 𝑩)(ν : hom 𝑨 𝑪)
  →             kernel ∣ ν ∣ ⊆ kernel ∣ τ ∣
  →             IsSurjective ∣ ν ∣ → IsSurjective ∣ τ ∣
                ---------------------------------------------
  →             Σ[ φ ∈ epi 𝑪 𝑩 ] ∀ x → ∣ τ ∣ x ≡ ∣ φ ∣ (∣ ν ∣ x)

 HomFactorEpi wd 𝑩 τ ν kerincl νe τe = (fst ∣ φF ∣ ,(snd ∣ φF ∣ , φE)), ∥ φF ∥
  where
   φF : Σ[ φ ∈ hom 𝑪 𝑩 ] ∀ x → ∣ τ ∣ x ≡ ∣ φ ∣ (∣ ν ∣ x)
   φF = HomFactor wd 𝑩 τ ν kerincl νe

   φ : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
   φ = ∣ τ ∣ ∘ (SurjInv ∣ ν ∣ νe)

   φE : IsSurjective φ
   φE = epic-factor ∣ τ ∣ ∣ ν ∣ φ ∥ φF ∥ τe

\end{code}

--------------------------------------

<span style="float:left;">[← Base.Homomorphisms.Noether](Base.Homomorphisms.Noether.html)</span>
<span style="float:right;">[Base.Homomorphisms.Isomorphisms →](Base.Homomorphisms.Isomorphisms.html)</span>

{% include UALib.Links.md %}
