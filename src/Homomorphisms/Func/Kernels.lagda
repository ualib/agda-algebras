---
layout: default
title : "Homomorphisms.Func.Kernels module (Agda Universal Algebra Library)"
date : "2021-09-13"
author: "agda-algebras development team"
---

#### <a id="kernels-of-homomorphisms-of-setoidalgebras">Kernels of Homomorphisms of SetoidAlgebras</a>

This is the [Homomorphisms.Func.Kernels][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using (𝓞 ; 𝓥 ; Signature )

module Homomorphisms.Func.Kernels {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ------------------------------------------
open import Agda.Primitive          using ( _⊔_ ) renaming ( Set to Type )
open import Data.Product      using ( _,_ )
open import Function          using ( _∘_ ; id )
open import Function.Bundles          using ( Func )
open import Level             using ( Level )
open import Relation.Binary   using ( Setoid )
open import Relation.Binary.PropositionalEquality using () renaming ( refl to ≡refl)

-- Imports from the Agda Universal Algebra Library ------------------------------------------
open import Overture.Preliminaries              using ( ∣_∣ ; ∥_∥ )
open import Overture.Func.Preliminaries              using ( _⟶_ ; 𝑖𝑑 )
open import Overture.Func.Inverses             using ( Image_∋_ )
open import Overture.Func.Surjective            using ( IsSurjective )
open import Relations.Discrete                  using ( kerRel ; kerRelOfEquiv )
open import Algebras.Setoid.Basic       {𝑆 = 𝑆} using ( SetoidAlgebra ; _̂_ )
open import Algebras.Func.Congruences {𝑆 = 𝑆} using ( _∣≈_ ; Con ; mkcon ; _╱_ ; IsCongruence ; /-≡ )
open import Homomorphisms.Func.Basic  {𝑆 = 𝑆} using ( hom ; IsHom ; epi ; IsEpi ; epi-to-hom )
open import Homomorphisms.Func.Properties {𝑆 = 𝑆} using ( 𝒾𝒹 )

private variable
 α β ρᵃ ρᵇ ℓ : Level

open SetoidAlgebra using ( Domain )
open Func using ( cong ) renaming (f to _⟨$⟩_ )

module _ {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ} (h : hom 𝑨 𝑩) where

 open Setoid (Domain 𝑨) using ( reflexive )                   renaming ( _≈_ to _≈₁_ )
 open SetoidAlgebra 𝑩   using ( Interp )                      renaming (Domain to B )
 open Setoid B          using ( sym ; trans ; isEquivalence ) renaming ( _≈_ to _≈₂_ )

 private
  hmap = _⟨$⟩_ ∣ h ∣

\end{code}

`HomKerComp` asserts that the kernel of a homomorphism is compatible with the basic operations.
That is, if each `(u i, v i)` belongs to the kernel, then so does the pair `((f ̂ 𝑨) u , (f ̂ 𝑨) v)`.

\begin{code}

 HomKerComp : 𝑨 ∣≈ (kerRel _≈₂_ hmap)
 HomKerComp f {u}{v} kuv = Goal
  where
  fhuv : ((f ̂ 𝑩)(hmap ∘ u)) ≈₂ ((f ̂ 𝑩)(hmap ∘ v))
  fhuv = cong Interp (≡refl , kuv)
  lem1 : (hmap ((f ̂ 𝑨) u)) ≈₂ ((f ̂ 𝑩) (hmap ∘ u))
  lem1 = IsHom.compatible ∥ h ∥

  lem2 : ((f ̂ 𝑩) (hmap ∘ v)) ≈₂ (hmap ((f ̂ 𝑨) v))
  lem2 = sym (IsHom.compatible ∥ h ∥)
  Goal : (hmap ((f ̂ 𝑨) u)) ≈₂ (hmap ((f ̂ 𝑨) v))
  Goal = trans lem1 (trans fhuv lem2)

\end{code}

The kernel of a homomorphism is a congruence of the domain, which we construct as follows.

\begin{code}

 kercon : Con 𝑨
 kercon = (kerRel _≈₂_ hmap) , mkcon (λ x → cong ∣ h ∣ x) (kerRelOfEquiv isEquivalence hmap) (HomKerComp)

\end{code}

Now that we have a congruence, we can construct the quotient relative to the kernel.

\begin{code}

 kerquo : SetoidAlgebra _ _
 kerquo = 𝑨 ╱ kercon

ker[_⇒_]_ : (𝑨 : SetoidAlgebra α ρᵃ) (𝑩 : SetoidAlgebra β ρᵇ)
 →          hom 𝑨 𝑩 → SetoidAlgebra _ _
ker[ 𝑨 ⇒ 𝑩 ] h = kerquo h
\end{code}


#### <a id="the-canonical-projection">The canonical projection</a>

Given an algebra `𝑨` and a congruence `θ`, the *canonical projection* is a map from `𝑨` onto `𝑨 ╱ θ` that is constructed, and proved epimorphic, as follows.

\begin{code}

module _ {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ} (h : hom 𝑨 𝑩) where

 open IsCongruence

 πepi : (θ : Con 𝑨 {ℓ}) → epi 𝑨 (𝑨 ╱ θ)
 πepi θ = p , pepi
  where

  open SetoidAlgebra (𝑨 ╱ θ) using () renaming ( Domain to A/θ )
  open Setoid A/θ            using ( sym ; refl )
  open IsHom {𝑨 = (𝑨 ╱ θ)}   using ( compatible )

  p : (Domain 𝑨) ⟶ A/θ
  p = record { f = id ; cong = reflexive ∥ θ ∥ }

  pepi : IsEpi 𝑨 (𝑨 ╱ θ) p
  pepi = record { isHom = record { compatible = sym (compatible ∥ 𝒾𝒹 ∥)
                                 ; preserves≈ = reflexive ∥ θ ∥ }
                ; isSurjective = λ {y} → Image_∋_.eq y refl }
 
\end{code}

In may happen that we don't care about the surjectivity of `πepi`, in which case would might prefer to work with the *homomorphic reduct* of `πepi`. This is obtained by applying `epi-to-hom`, like so.

\begin{code}

 πhom : (θ : Con 𝑨 {ℓ}) → hom 𝑨 (𝑨 ╱ θ)
 πhom θ = epi-to-hom 𝑨 (𝑨 ╱ θ) (πepi θ)

\end{code}


We combine the foregoing to define a function that takes 𝑆-algebras `𝑨` and `𝑩`, and a homomorphism `h : hom 𝑨 𝑩` and returns the canonical epimorphism from `𝑨` onto `𝑨 [ 𝑩 ]/ker h`. (Recall, the latter is the special notation we defined above for the quotient of `𝑨` modulo the kernel of `h`.)

\begin{code}

 πker : (h : hom 𝑨 𝑩) → epi 𝑨 (ker[ 𝑨 ⇒ 𝑩 ] h)
 πker h = πepi (kercon h)

\end{code}

The kernel of the canonical projection of `𝑨` onto `𝑨 / θ` is equal to `θ`, but since equality of inhabitants of certain types (like `Congruence` or `Rel`) can be a tricky business, we settle for proving the containment `𝑨 / θ ⊆ θ`. Of the two containments, this is the easier one to prove; luckily it is also the one we need later.

\begin{code}

 open IsCongruence

 ker-in-con : {θ : Con 𝑨 {ℓ}}
  →           ∀ {x}{y} → ∣ kercon (πhom θ) ∣ x y →  ∣ θ ∣ x y

 ker-in-con = id

\end{code}




--------------------------------

<span style="float:left;">[← Homomorphisms.Func.Properties](Homomorphisms.Func.Properties.html)</span>
<span style="float:right;">[Homomorphisms.Func.Factor →](Homomorphisms.Func.Factor.html)</span>

{% include UALib.Links.md %}
