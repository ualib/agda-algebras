---
layout: default
title : "Varieties.Setoid.FreeAlgebras module (Agda Universal Algebra Library)"
date : "2021-06-29"
author: "agda-algebras development team"
---

#### <a id="free-setoid-algebras">Free setoid algebras</a>

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Varieties.Setoid.FreeAlgebras {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ------------------------------------------------
open import Agda.Primitive   using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type )
open import Data.Product     using ( _,_ ; Σ-syntax ) renaming ( proj₂ to snd )
open import Function.Bundles using ( Func )
open import Relation.Binary  using ( Setoid )
open import Relation.Unary   using ( Pred )
import Relation.Binary.PropositionalEquality as ≡

-- Imports from the Agda Universal Algebra Library ---------------------------------------------------
open import Overture.Preliminaries                   using ( ∣_∣ )
open import Overture.Func.Preliminaries              using ( _⟶_ )
open import Overture.Func.Inverses                   using ( Image_∋_ )
open import Overture.Func.Surjective                 using ( IsSurjective )
open import Algebras.Func.Basic              {𝑆 = 𝑆} using ( SetoidAlgebra ; ov )
open import Homomorphisms.Func.Basic         {𝑆 = 𝑆} using ( hom ; epi ; IsEpi ; IsHom ; epi-to-hom )
open import Terms.Basic                      {𝑆 = 𝑆} using ( Term )
open import Terms.Func.Basic                 {𝑆 = 𝑆} using ( 𝑻 ; _≐_ ; module Environment )
open import Varieties.Setoid.EquationalLogic {𝑆 = 𝑆} using ( Eq ; _⊫_ ; module FreeAlgebra )
private variable
 α χ ρ ℓ : Level

module _ {X : Type χ}{𝒦 : Pred (SetoidAlgebra α ρ) ℓ} where

 -- ℐ indexes the collection of equations modeled by 𝒦
 ℐ : Type (ℓ ⊔ ov(α ⊔ χ ⊔ ρ))
 ℐ = Σ[ eq ∈ Eq{χ} ] 𝒦 ⊫ eq

 ℰ : ℐ → Eq
 ℰ (eqv , p) = eqv

\end{code}

We now define the algebra `𝔽`, which plays the role of the relatively free algebra, along with the natural epimorphism `epi𝔽 : epi (𝑻 X) 𝔽` from `𝑻 X` to `𝔽`.
The relatively free algebra (relative to `Th 𝒦`) is called `M` and is derived from `TermSetoid X` and `TermInterp X` and imported from the EquationalLogic module.

\begin{code}
 open _≐_
 open FreeAlgebra {X = X}{ι = (ℓ ⊔ ov(α ⊔ χ ⊔ ρ))}{I = ℐ} ℰ

 open SetoidAlgebra 𝔽[ X ] using ( Interp ) renaming ( Domain to 𝔽 )
 open Environment 𝔽[ X ]
 open Setoid 𝔽 using ( _≈_ ; reflexive ) renaming ( refl to reflF )
 open SetoidAlgebra (𝑻 X) using () renaming (Domain to 𝕋)
 open Setoid 𝕋 using () renaming ( _≈_ to _≃_ ; refl to reflT )
 open Func using ( cong ) renaming ( f to _⟨$⟩_ )
 open Term
 epi𝔽 : epi (𝑻 X) 𝔽[ X ]
 epi𝔽 = h , hepi
  where
  c : ∀ {x y} → x ≃ y → x ≈ y
  c (_≐_.refl {x} {.x} ≡.refl) = reflF
  c (genl {f}{s}{t} x) = cong Interp (≡.refl , (λ i → c (x i)))

  h : 𝕋 ⟶ 𝔽
  h ⟨$⟩ t = t
  cong h = c

  open IsEpi
  hepi : IsEpi (𝑻 X) 𝔽[ X ] h
  IsHom.compatible (isHom hepi) {f}{a} = cong Interp (≡.refl , (λ i → reflF))
  IsHom.preserves≈ (isHom hepi) = c
  isSurjective hepi {y} = Image_∋_.eq y reflF


 hom𝔽 : hom (𝑻 X) 𝔽[ X ]
 hom𝔽 = epi-to-hom (𝑻 X) 𝔽[ X ] epi𝔽

 hom𝔽-is-epic : IsSurjective ∣ hom𝔽 ∣
 hom𝔽-is-epic = IsEpi.isSurjective (snd (epi𝔽))

 -- 𝕍𝒦 : Pred (SetoidAlgebra _ _) _
 -- 𝕍𝒦 = V 𝒦
 -- 𝔽-ModTh-epi : (𝑨 : SetoidAlgebra _ _) → 𝑨 ∈ Mod (Th 𝕍𝒦) → epi 𝔽 𝑨
 -- 𝔽-ModTh-epi 𝑨 AinMTV = ?
\end{code}

To be continued...

(TODO: complete this module)

--------------------------------

<span style="float:left;">[← Varieties.Setoid.Closure](Varieties.Setoid.Closure.html)</span>
<span style="float:right;">[Structures →](Structures.html)</span>

{% include UALib.Links.md %}
