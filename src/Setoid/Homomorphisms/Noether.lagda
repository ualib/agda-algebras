---
layout: default
title : "Setoid.Homomorphisms.Noether module (The Agda Universal Algebra Library)"
date : "2021-09-15"
author: "agda-algebras development team"
---

### <a id="homomorphism-theorems">Homomorphism Theorems for Setoid Algebras</a>

This is the [Setoid.Homomorphisms.Noether][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Base.Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Homomorphisms.Noether {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ---------------------------
open import Agda.Primitive    using ( Level )
open import Data.Product      using (Σ-syntax ; _,_ )  renaming ( _×_ to _∧_ )
open import Function.Base     using ( id )
open import Function.Bundles  using ()                 renaming ( Func to _⟶_ )
open import Relation.Binary   using ( Setoid )
open import Relation.Binary.PropositionalEquality as ≡ using ( _≡_ )
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from agda-algebras ------------------------------------------------
open import Base.Overture.Preliminaries                 using ( ∣_∣ ; ∥_∥ )
open import Setoid.Overture.Injective              using ( IsInjective )
open import Setoid.Algebras.Basic                  using ( Algebra ; _̂_)
open import Setoid.Homomorphisms.Basic    {𝑆 = 𝑆}  using ( hom ; IsHom )
open import Setoid.Homomorphisms.Kernels  {𝑆 = 𝑆}  using ( kerquo ; πker )

private variable
 α ρᵃ β ρᵇ γ ρᶜ ι : Level

\end{code}

#### <a id="the-first-homomorphism-theorem">The First Homomorphism Theorem for setoid algebras</a>

\begin{code}

open _⟶_ using ( cong ) renaming ( f to _⟨$⟩_ )
open Algebra using ( Domain )

module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}(hh : hom 𝑨 𝑩) where
 open Algebra 𝑩 using ( Interp ) renaming ( Domain to B )
 open Setoid B using ( _≈_ ; refl ; sym ; trans ) -- renaming ( _≈_ to _≈₂_ )
 open Algebra (kerquo hh) using () renaming ( Domain to A/hKer )

 open IsHom
 private
  hfunc = ∣ hh ∣
  h = _⟨$⟩_ hfunc

 FirstHomTheorem : Σ[ φ ∈ hom (kerquo hh) 𝑩  ]
                    (∀ a → h a ≈ ∣ φ ∣ ⟨$⟩ (∣ πker hh ∣ ⟨$⟩ a))
                    ∧ IsInjective ∣ φ ∣

 FirstHomTheorem = (φ , φhom) , (λ _ → refl) , φmon
  where
  φ : A/hKer ⟶ B
  _⟨$⟩_ φ = h
  cong φ = id

  φhom : IsHom (kerquo hh) 𝑩 φ
  compatible φhom = trans (compatible ∥ hh ∥) (cong Interp (≡.refl , (λ _ → refl)))

  φmon : IsInjective φ
  φmon = id

\end{code}

Now we prove that the homomorphism whose existence is guaranteed by `FirstHomTheorem` is unique.

\begin{code}

 FirstHomUnique : (f g : hom (kerquo hh) 𝑩)
  →                 (∀ a →  h a ≈ ∣ f ∣ ⟨$⟩ (∣ πker hh ∣ ⟨$⟩ a))
  →                 (∀ a →  h a ≈ ∣ g ∣ ⟨$⟩ (∣ πker hh ∣ ⟨$⟩ a))
  →                 ∀ [a]  →  ∣ f ∣ ⟨$⟩ [a] ≈ ∣ g ∣ ⟨$⟩ [a]

 FirstHomUnique fh gh hfk hgk a = trans (sym (hfk a)) (hgk a)

\end{code}

--------------------------------------

<span style="float:left;">[← Setoid.Homomorphisms.Products](Setoid.Homomorphisms.Products.html)</span>
<span style="float:right;">[Setoid.Homomorphisms.Factor →](Setoid.Homomorphisms.Factor.html)</span>

{% include UALib.Links.md %}
