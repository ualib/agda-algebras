---
layout: default
title : Algebras.Setoid.Products module (Agda Universal Algebra Library)
date : 2021-07-03
author: [agda-algebras development team][]
---

#### <a id="products-of-setoidalgebras">Products of Setoid Algebras</a>

This is the [Algebras.Setoid.Products][] module of the [Agda Universal Algebra Library][].


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


open import Algebras.Basic using (𝓞 ; 𝓥 ; Signature)

module Algebras.Setoid.Products {𝑆 : Signature 𝓞 𝓥} where

-- Imports from the Agda Standard Library ---------------------
open import Agda.Primitive   using ( lsuc ; _⊔_ ; Level ) renaming ( Set to Type )
open import Data.Product     using ( _,_ ; Σ ; Σ-syntax )
open import Function.Base    using ( flip )
open import Function.Bundles using ( Func )
open import Relation.Binary  using ( Setoid ;  IsEquivalence )
open import Relation.Binary.PropositionalEquality
                             using ( refl )
open import Relation.Unary   using ( Pred ; _⊆_ ; _∈_ )

-- Imports from agda-algebras --------------------------------------------------------------
open import Overture.Preliminaries        using ( ∣_∣; ∥_∥)
open import Algebras.Setoid.Basic {𝑆 = 𝑆} using ( Algebroid ; ⟦_⟧ ; SetoidAlgebra ; _̂_ ; ov )

open Func          using ( cong ) renaming ( f to _<$>_ )
open Setoid        using ( Carrier ; _≈_ ) renaming ( isEquivalence to isEqv )
open IsEquivalence using () renaming ( refl to reflE ; sym to symE ; trans to transE )

private variable α ρ ι : Level

\end{code}

##### <a id="products-of-setoidalgebras">Products of SetoidAlgebras</a>

\begin{code}

open SetoidAlgebra

⨅ : {I : Type ι }(𝒜 : I → SetoidAlgebra α ρ) → SetoidAlgebra (α ⊔ ι) (ρ ⊔ ι)

Domain (⨅ {I} 𝒜) =

 record { Carrier = ∀ i → Carrier (Domain (𝒜 i))

        ; _≈_ = λ a b → ∀ i → Domain (𝒜 i) ._≈_ (a i) (b i)

        ; isEquivalence =
           record { refl  =     λ i → reflE  (isEqv (Domain (𝒜 i)))
                  ; sym   =   λ x i → symE   (isEqv (Domain (𝒜 i)))(x i)
                  ; trans = λ x y i → transE (isEqv (Domain (𝒜 i)))(x i)(y i)
                  }
        }

(Interp (⨅ {I} 𝒜)) <$> (f , a) = λ i → (f ̂ (𝒜 i)) (flip a i)
cong (Interp (⨅ {I} 𝒜)) (refl , f=g ) = λ i → cong  (Interp (𝒜 i)) (refl , flip f=g i )

\end{code}


##### <a id="products-of-classes-of-setoidalgebras">Products of classes of SetoidAlgebras</a>

\begin{code}

module _ {𝒦 : Pred (SetoidAlgebra α ρ) (ov α)} where

 ℑ : Type (ov(α ⊔ ρ))
 ℑ = Σ[ 𝑨 ∈ (SetoidAlgebra α ρ) ] 𝑨 ∈ 𝒦


 𝔄 : ℑ → SetoidAlgebra α ρ
 𝔄 i = ∣ i ∣

 class-product : SetoidAlgebra (ov (α ⊔ ρ)) _
 class-product = ⨅ 𝔄

\end{code}

If `p : 𝑨 ∈ 𝒦`, we view the pair `(𝑨 , p) ∈ ℑ` as an *index* over the class,
so we can think of `𝔄 (𝑨 , p)` (which is simply `𝑨`) as the projection of the
product `⨅ 𝔄` onto the `(𝑨 , p)`-th component.


##### <a id="products-of-algebroids">Products of Algebroids</a>

\begin{code}

⨅oid : {I : Type ι }(𝒜 : I → Algebroid α ρ) → Algebroid (α ⊔ ι) (ρ ⊔ ι)

⨅oid {I} 𝒜 = domain , interp
 where
 domain : Setoid _ _
 domain = record { Carrier = ∀ i → Carrier ∣ 𝒜 i ∣
                 ; _≈_ = λ u v  → ∀ i → (_≈_ ∣ 𝒜 i ∣) (u i) (v i)
                 ; isEquivalence =
                    record { refl  =     λ i → reflE  (isEqv ∣ 𝒜 i ∣)
                           ; sym   =   λ x i → symE   (isEqv ∣ 𝒜 i ∣)(x i)
                           ; trans = λ u v i → transE (isEqv ∣ 𝒜 i ∣)(u i)(v i)
                           }
                 }

 interp : Func (⟦ 𝑆 ⟧ domain) domain
 interp <$> (f , as ) = λ i → ∥ 𝒜 i ∥ <$> (f , (flip as i ))
 cong  interp (refl , f=g) i = cong  ∥ 𝒜 i ∥ (refl , (flip f=g i))

\end{code}

##### <a id="products-of-classes-of-algebroids">Products of classes of Algebroids</a>

\begin{code}

module _ {𝒦 : Pred (Algebroid α ρ) (𝓞 ⊔ 𝓥 ⊔ lsuc α)} where

 ℑ' : Type (ov(α ⊔ ρ))
 ℑ' = Σ[ 𝑨 ∈ (Algebroid α ρ) ] 𝑨 ∈ 𝒦


 𝔄' : ℑ' → Algebroid α ρ
 𝔄' i = ∣ i ∣

 class-product' : Algebroid (ov (α ⊔ ρ)) _
 class-product' = ⨅oid 𝔄'

\end{code}

--------------------------------

<br>

[← Algebras.Setoid.Basic](Algebras.Setoid.Basic.html)
<span style="float:right;">[Algebras.Setoid.Congruences →](Algebras.Setoid.Congruences.html)</span>

{% include UALib.Links.md %}

