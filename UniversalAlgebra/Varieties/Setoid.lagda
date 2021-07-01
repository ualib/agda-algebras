---
layout: default
title : Varieties.Setoid module (Agda Universal Algebra Library)
date : 2021-06-29
author: [the agda-algebras development team][]
---

### Free Algebras and Birkhoff's Theorem (Setoid version)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


open import Level using (Level)
open import Algebras.Basic

module Varieties.Setoid {α 𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥) where


-- Imports from Agda (builtin/primitive) and the Agda Standard Library ---------------------
open import Agda.Primitive          renaming ( Set to Type )
                                    using    ( _⊔_ )
open import Data.Product            using    ( _,_ ; Σ-syntax ; Σ ; _×_ )
                                    renaming ( proj₁ to fst
                                             ; proj₂ to snd )
open import Relation.Unary          using    ( Pred ; _∈_ ) -- ; _⊆_ ; ｛_｝ ; _∪_ )

-- Imports from the Agda Universal Algebra Library -------------------------------------------
open import Overture.Preliminaries       using ( ∣_∣ ) -- ; ∥_∥ ; _∙_ ; _⁻¹ )
open import Algebras.Products          {𝑆 = 𝑆} using ( ov ) 
open import Algebras.Setoid      {𝑆 = 𝑆} using ( SetoidAlgebra ; ⟦_⟧s ; ⨅')
open import Homomorphisms.Basic        {𝑆 = 𝑆} using ( hom ; epi ) -- ⨅-hom-co ; ker[_⇒_]_↾_ ; 
open import Varieties.EquationalLogic     {𝑆 = 𝑆} using ( Eq ; _⊫_ ; module TermModel)

private variable
 χ ρ ℓ : Level

module _ {Γ : Type χ}{𝒦 : Pred (SetoidAlgebra α ρ) ℓ} where

 -- I indexes the collection of equations modeled by 𝒦
 ℐ : Type (ℓ ⊔ ov(α ⊔ χ ⊔ ρ))
 ℐ = Σ[ eq ∈ Eq{χ} ] 𝒦 ⊫ eq

 ℰ : ℐ → Eq
 ℰ (eq , p) = eq

\end{code}

#### The free algebra

We now define the algebra `𝔽`, which plays the role of the relatively free algebra, along with the natural epimorphism `epi𝔽 : epi (𝑻 X) 𝔽` from `𝑻 X` to `𝔽`.

\begin{code}

 -- The relatively free algebra (relative to Th 𝒦) is called `M`
 -- and is derived from `TermSetoid Γ` and `TermInterp Γ` and
 -- imported from the EquationalLogic module.
 open TermModel {ι = (ℓ ⊔ ov(α ⊔ χ ⊔ ρ))}{Γ = Γ}{I = ℐ} ℰ

 𝔽 : SetoidAlgebra _ _
 𝔽 = M Γ

 -- epi𝔽 : epi TermSetoid(𝑻 X) 𝔽
 -- epi𝔽 = ?

 -- hom𝔽 : hom (𝑻 X) 𝔽
 -- hom𝔽 = epi-to-hom 𝔽 epi𝔽

 -- hom𝔽-is-epic : IsSurjective ∣ hom𝔽 ∣
 -- hom𝔽-is-epic = snd ∥ epi𝔽 ∥

\end{code}


----------------------------

[the agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
