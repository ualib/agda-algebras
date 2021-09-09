---
layout: default
title : "Homomorphisms.Setoid.Properties module (Agda Universal Algebra Library)"
date : "2021-09-08"
author: "agda-algebras development team"
---

#### <a id="properties-of-homomorphisms-of-setoidalgebras">Properties of Homomorphisms of SetoidAlgebras</a>

This is the [Homomorphisms.Setoid.Properties][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using (𝓞 ; 𝓥 ; Signature )

module Homomorphisms.Setoid.Properties {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ------------------------------------------
open import Data.Product    using ( _,_ ; Σ ; Σ-syntax ; _×_ ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Function        using ( _∘_ ; id )
open import Level           using ( Level )
open import Relation.Binary using (  Setoid )
open import Relation.Binary.PropositionalEquality as PE
                            using ( _≡_ ; refl ; module ≡-Reasoning )

-- Imports from the Agda Universal Algebra Library ------------------------------------------
open import Algebras.Setoid.Basic      {𝑆 = 𝑆} using ( 𝕌[_] ; SetoidAlgebra ; _̂_ ; Lift-Alg )
open import Homomorphisms.Setoid.Basic {𝑆 = 𝑆} using ( IsHom ; hom ; compatible-map ; ≈preserving )

private variable
 α β γ ρ ρᵃ ρᵇ ρᶜ ℓ : Level

\end{code}


##### <a id="composition-of-homs">Composition of homs</a>

\begin{code}

module _ (𝑨 : SetoidAlgebra α ρᵃ)
         (𝑩 : SetoidAlgebra β ρᵇ)
         (𝑪 : SetoidAlgebra γ ρᶜ)
         where

 open Setoid
 open SetoidAlgebra
 open IsHom

 -- The composition of homomorphisms is again a homomorphism
 ∘-is-hom : {g : 𝕌[ 𝑨 ] → 𝕌[ 𝑩 ]}{h : 𝕌[ 𝑩 ] → 𝕌[ 𝑪 ]}
  →         IsHom 𝑨 𝑩 g → IsHom 𝑩 𝑪 h
            -------------------------------------------------
  →         IsHom 𝑨 𝑪 (h ∘ g)

 ∘-is-hom {g} {h} ghom hhom = record { compatible = i ; preserves≈ = ii }
  where
  i : compatible-map 𝑨 𝑪 (h ∘ g)
  i f a = trans (Domain 𝑪) lemg lemh
   where
   lemg : (_≈_ (Domain 𝑪)) (h (g ((f ̂ 𝑨) a))) (h ((f ̂ 𝑩) (λ x → g (a x))))
   lemg = preserves≈ hhom (compatible ghom f a)

   lemh : (_≈_ (Domain 𝑪)) (h ((f ̂ 𝑩) (λ x → g (a x)))) ((f ̂ 𝑪) (λ x → h (g (a x))))
   lemh = compatible hhom f (g ∘ a)


  ii : ≈preserving 𝑨 𝑪 (h ∘ g)
  ii xy = preserves≈ hhom (preserves≈ ghom xy)

 ∘-hom : hom 𝑨 𝑩 → hom 𝑩 𝑪  → hom 𝑨 𝑪
 ∘-hom (h , hhom) (g , ghom) = (g ∘ h) , ∘-is-hom hhom ghom

\end{code}



##### <a id="lifting-and-lowering">Lifting and lowering of homs</a>

First we define the identity homomorphism for setoid algebras and then we prove that the operations of lifting and lowering of a setoid algebra are homomorphisms.

\begin{code}

-- setoid-based version
open SetoidAlgebra

𝒾𝒹 :  (𝑨 : SetoidAlgebra α ρ) → hom 𝑨 𝑨
𝒾𝒹 𝑨 = id , record { compatible = λ f a → Setoid.reflexive (Domain 𝑨) refl
                   ; preserves≈ = id }

open Level
𝓁𝒾𝒻𝓉 : {𝑨 : SetoidAlgebra α ρ} → hom 𝑨 (Lift-Alg 𝑨 ℓ)
𝓁𝒾𝒻𝓉 {𝑨 = 𝑨} = lift , record { compatible = λ f a → Setoid.reflexive (Domain 𝑨) refl
                             ; preserves≈ = id }

𝓁ℴ𝓌ℯ𝓇 : {𝑨 : SetoidAlgebra α ρ} → hom (Lift-Alg 𝑨 ℓ) 𝑨
𝓁ℴ𝓌ℯ𝓇 {ℓ = ℓ}{𝑨} = lower , record { compatible = λ f a → Setoid.reflexive (Domain (Lift-Alg 𝑨 ℓ)) refl
                                  ; preserves≈ = id }
\end{code}


Next we formalize the fact that a homomorphism from `𝑨` to `𝑩` can be lifted to a homomorphism from `Lift-Alg 𝑨 ℓᵃ` to `Lift-Alg 𝑩 ℓᵇ`.

\begin{code}

module _ {𝑨 : SetoidAlgebra α ρᵃ} {𝑩 : SetoidAlgebra β ρᵇ} where
 open Level

 Lift-hom : hom 𝑨 𝑩  → (ℓᵃ ℓᵇ : Level) →  hom (Lift-Alg 𝑨 ℓᵃ) (Lift-Alg 𝑩 ℓᵇ)
 Lift-hom (f , fhom) ℓᵃ ℓᵇ = (lift ∘ f ∘ lower) , Goal
  where
  lA lB : SetoidAlgebra _ _
  lA = Lift-Alg 𝑨 ℓᵃ
  lB = Lift-Alg 𝑩 ℓᵇ

  lABh : IsHom lA 𝑩 (f ∘ lower)
  lABh = ∘-is-hom lA 𝑨 𝑩 (snd 𝓁ℴ𝓌ℯ𝓇) fhom

  Goal : IsHom lA lB (lift ∘ (f ∘ lower))
  Goal = ∘-is-hom lA 𝑩 lB lABh (snd 𝓁𝒾𝒻𝓉)

\end{code}

--------------------------------

<span style="float:left;">[← Homomorphisms.Setoid.Basic](Homomorphisms.Setoid.Basic.html)</span>
<span style="float:right;">[Homomorphisms.Setoid.Kernels →](Homomorphisms.Setoid.Kernels.html)</span>

{% include UALib.Links.md %}
