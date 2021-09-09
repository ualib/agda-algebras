---
layout: default
title : "Homomorphisms.Setoid.Kernels module (Agda Universal Algebra Library)"
date : "2021-09-08"
author: "agda-algebras development team"
---

#### <a id="kernels-of-homomorphisms-of-setoidalgebras">Kernels of Homomorphisms of SetoidAlgebras</a>

This is the [Homomorphisms.Setoid.Kernels][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using (𝓞 ; 𝓥 ; Signature )

module Homomorphisms.Setoid.Kernels {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ------------------------------------------
open import Data.Product      using ( _,_ )
open import Function          using ( Func ; _∘_ )
open import Level             using ( Level )
open import Relation.Binary   using ( Setoid )
open import Relation.Binary.PropositionalEquality as PE using ()

-- Imports from the Agda Universal Algebra Library ------------------------------------------
open import Overture.Preliminaries              using ( ∣_∣ ; ∥_∥ )
open import Relations.Discrete                  using ( kerRel ; kerRelOfEquiv )
open import Algebras.Setoid.Basic       {𝑆 = 𝑆} using ( SetoidAlgebra ; 𝕌[_] ; _̂_ )
open import Algebras.Setoid.Congruences {𝑆 = 𝑆} using ( _∣≈_ ; Con ; mkcon ; _╱_ )
open import Homomorphisms.Setoid.Basic  {𝑆 = 𝑆} using ( hom ; IsHom )
private variable
 α β ρ ρᵃ ρᵇ : Level

module _ (𝑨 : SetoidAlgebra α ρᵃ) (𝑩 : SetoidAlgebra β ρᵇ) where
 open SetoidAlgebra
 open Setoid
 open Func
 private
  A = 𝕌[ 𝑨 ]
  B = 𝕌[ 𝑩 ]
  ≈B = _≈_ (Domain 𝑩)
 HomKerComp : (h : hom 𝑨 𝑩) → 𝑨 ∣≈ (kerRel ≈B ∣ h ∣)
 HomKerComp h f {u}{v} kuv = Goal
  where
  fhuv : ≈B ((f ̂ 𝑩)(∣ h ∣ ∘ u)) ((f ̂ 𝑩)(∣ h ∣ ∘ v))
  fhuv = cong (Interp 𝑩) (PE.refl , kuv)
  lem1 : ≈B (∣ h ∣ ((f ̂ 𝑨) u)) ((f ̂ 𝑩) (∣ h ∣ ∘ u))
  lem1 = IsHom.compatible ∥ h ∥ f u

  lem2 : ≈B ((f ̂ 𝑩) (∣ h ∣ ∘ v)) (∣ h ∣ ((f ̂ 𝑨) v))
  lem2 = (sym (Domain 𝑩)) (IsHom.compatible ∥ h ∥ f v)
  Goal : ≈B (∣ h ∣ ((f ̂ 𝑨) u)) (∣ h ∣ ((f ̂ 𝑨) v))
  Goal = trans (Domain 𝑩) lem1 (trans (Domain 𝑩) fhuv lem2)

 kercon : hom 𝑨 𝑩 → Con 𝑨
 kercon h = (kerRel ≈B ∣ h ∣) , mkcon (kerRelOfEquiv (isEquivalence (Domain 𝑩)) ∣ h ∣) (HomKerComp h)

 kerquo : hom 𝑨 𝑩 → SetoidAlgebra _ _
 kerquo h = 𝑨 ╱ (kercon h)

ker[_⇒_]_ : (𝑨 : SetoidAlgebra α ρᵃ) (𝑩 : SetoidAlgebra β ρᵇ)
 →          hom 𝑨 𝑩 → SetoidAlgebra _ _
ker[ 𝑨 ⇒ 𝑩 ] h = kerquo 𝑨 𝑩 h
\end{code}

--------------------------------

<span style="float:left;">[← Homomorphisms.Setoid.Properties](Homomorphisms.Setoid.Properties.html)</span>
<span style="float:right;">[Homomorphisms.Setoid.Factor →](Homomorphisms.Setoid.Factor.html)</span>

{% include UALib.Links.md %}
