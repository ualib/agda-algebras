---
layout: default
title : Varieties.Setoid.FreeAlgebras module (Agda Universal Algebra Library)
date : 2021-06-29
author: [agda-algebras development team][]
---

### Free Algebras and Birkhoff's Theorem (Setoid version)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


open import Level using (Level)
open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Varieties.Setoid.FreeAlgebras {𝑆 : Signature 𝓞 𝓥} where


-- Imports from Agda (builtin/primitive) and the Agda Standard Library ---------------------
open import Agda.Builtin.Equality       using    ( _≡_       ;  refl )
open import Agda.Primitive using ( _⊔_ ; lsuc ) renaming ( Set to Type )
open import Data.Product            using    ( _,_   ; Σ-syntax
                                             ; Σ     ; _×_      )
                                    renaming ( proj₁ to fst
                                             ; proj₂ to snd     )
open import Function.Base           using    ( id )
open import Relation.Unary          using    ( Pred  ; _∈_      )

-- Imports from the Agda Universal Algebra Library -------------------------------------------
open import Overture.Preliminaries             using ( ∣_∣ )
open import Overture.Inverses                  using ( IsSurjective ; Image_∋_ ; Inv ; InvIsInv ; eq )
open import Algebras.Setoid.Products   {𝑆 = 𝑆} using ( ⨅ )
open import Algebras.Setoid.Basic      {𝑆 = 𝑆} using ( SetoidAlgebra ; ⟦_⟧s )
open import Homomorphisms.Setoid.Basic {𝑆 = 𝑆} using ( hom ; epi )
open import Terms.Setoid.Basic         {𝑆 = 𝑆} using ( TermAlgebra )
open import Varieties.Setoid.EquationalLogic {𝑆 = 𝑆} using ( Eq ; _⊫_ ; module TermModel ; Mod ; Th)

private variable
 α χ ρ ℓ : Level

ov : Level → Level
ov α = 𝓞 ⊔ 𝓥 ⊔ lsuc α



module _ {Γ : Type χ}{𝒦 : Pred (SetoidAlgebra α ρ) ℓ} where

 -- ℐ indexes the collection of equations modeled by 𝒦
 ℐ : Type (ℓ ⊔ ov(α ⊔ χ ⊔ ρ))
 ℐ = Σ[ eq ∈ Eq{χ} ] 𝒦 ⊫ eq

 ℰ : ℐ → Eq
 ℰ (eqv , p) = eqv

\end{code}

#### The free algebra

We now define the algebra `𝔽`, which plays the role of the relatively free algebra, along with the natural epimorphism `epi𝔽 : epi (𝑻 X) 𝔽` from `𝑻 X` to `𝔽`.

\begin{code}

 -- The relatively free algebra (relative to Th 𝒦) is called `M`
 -- and is derived from `TermSetoid Γ` and `TermInterp Γ` and
 -- imported from the EquationalLogic module.
 open TermModel {Γ = Γ}{ι = (ℓ ⊔ ov(α ⊔ χ ⊔ ρ))}{I = ℐ} ℰ

 𝔽 : SetoidAlgebra _ _
 𝔽 = M Γ

 epi𝔽 : epi (TermAlgebra Γ) 𝔽
 epi𝔽 = record { map = id ; is-epi = (λ 𝑓 a → refl) , λ y → eq y refl }

 open epi

 hom𝔽 : hom (TermAlgebra Γ) 𝔽
 hom𝔽 = epi-to-hom epi𝔽

 hom𝔽-is-epic : IsSurjective ∣ hom𝔽 ∣
 hom𝔽-is-epic = snd (is-epi epi𝔽)

 -- 𝕍𝒦 : Pred (SetoidAlgebra _ _) _
 -- 𝕍𝒦 = V 𝒦

 -- 𝔽-ModTh-epi : (𝑨 : SetoidAlgebra _ _) → 𝑨 ∈ Mod (Th 𝕍𝒦) → epi 𝔽 𝑨
 -- 𝔽-ModTh-epi 𝑨 AinMTV = ?


\end{code}


----------------------------

[the agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
