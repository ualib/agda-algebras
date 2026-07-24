---
layout: default
title : "Setoid.Algebras.Products module (Agda Universal Algebra Library)"
date : "2021-07-03"
author: "agda-algebras development team"
---

#### Products of Setoid Algebras

This is the [Setoid.Algebras.Products][] module of the [Agda Universal Algebra Library][].


<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Algebras.Products where

-- Imports from Agda and the Agda Standard Library --------------------------------
open import Agda.Primitive    using () renaming ( Set to Type )
open import Data.Product      using ( _,_ ; Σ-syntax ; proj₁ )
open import Function          using ( flip ; Func )
open import Level             using( _⊔_ ; Level )
open import Relation.Binary   using ( Setoid ;  IsEquivalence ; Decidable )
open import Relation.Binary.PropositionalEquality  using ( refl ; _≡_ )
open import Relation.Unary    using ( Pred ; _∈_ )

open Func           using ( cong ) renaming ( to to _⟨$⟩_ )
open Setoid         using ( Carrier ; _≈_ ) renaming ( isEquivalence to isEqv )
open IsEquivalence  using () renaming ( refl to reflE ; sym to symE ; trans to transE )


-- Imports from agda-algebras -----------------------------------------------------
open import Overture               using ( proj ; projIsOnto ; 𝓞 ; 𝓥 ; Signature ; 𝑆 )
                                   renaming ( IsSurjective to onto )

open import Setoid.Algebras.Basic  using ( Algebra ; _^_ ; ov ; 𝔻[_] ; 𝕌[_])

private variable α ρ ι : Level

open Algebra
```
-->

```agda
⨅ : {I : Type ι }(𝒜 : I → Algebra {𝑆 = 𝑆} α ρ) → Algebra {𝑆 = 𝑆} (α ⊔ ι) (ρ ⊔ ι)

Domain (⨅ {I} 𝒜) =
  record  { Carrier = ∀ i → 𝕌[ 𝒜 i ]
          ; _≈_ = λ a b → ∀ i → 𝔻[ 𝒜 i ] ._≈_ (a i) (b i)
          ; isEquivalence =
             record  { refl   = λ i      → reflE   (isEqv 𝔻[ 𝒜 i ])
                     ; sym    = λ x i    → symE    (isEqv 𝔻[ 𝒜 i ])(x i)
                     ; trans  = λ x y i  → transE  (isEqv 𝔻[ 𝒜 i ])(x i)(y i)
                     }
          }

Interp (⨅ {I} 𝒜) ⟨$⟩ (f , a) = λ i → (f ^ 𝒜 i) (flip a i)
cong (Interp (⨅ {I} 𝒜)) (refl , f=g ) = λ i → cong  (Interp (𝒜 i)) (refl , flip f=g i )
```


#### Products of classes of Algebras


```agda
module _ {𝑆 : Signature 𝓞 𝓥}{𝒦 : Pred (Algebra {𝑆 = 𝑆} α ρ) (ov {𝑆 = 𝑆} α)} where

  ℑ : Type (ov {𝑆 = 𝑆} (α ⊔ ρ))
  ℑ = Σ[ 𝑨 ∈ (Algebra {𝑆 = 𝑆} α ρ) ] 𝑨 ∈ 𝒦

  𝔄 : ℑ → Algebra {𝑆 = 𝑆} α ρ
  𝔄 i = (proj₁ i)

  class-product : Algebra {𝑆 = 𝑆} (ov {𝑆 = 𝑆} (α ⊔ ρ)) _
  class-product = ⨅ 𝔄
```


If `p : 𝑨 ∈ 𝒦`, we view the pair `(𝑨 , p) ∈ ℑ` as an *index* over the class,
so we can think of `𝔄 (𝑨 , p)` (which is simply `𝑨`) as the projection of the
product `⨅ 𝔄` onto the `(𝑨 , p)`-th component.

#### Surjectivity of coordinate projections

Suppose `I` is an index type and `𝒜 : I → Algebra α ρ` is an indexed collection of algebras.
Let `⨅ 𝒜` be the product algebra defined above.  Given `i : I`, consider the projection of `⨅ 𝒜`
onto the `i-th` coordinate.  Of course this projection ought to be a surjective map from `⨅ 𝒜` onto
`𝒜 i`.  However, this is impossible if `I` is just an arbitrary type.  Indeed, we must have an
equality defined on `I` and this equality must be decidable, and we must assume that
each factor of the product is nonempty.  In the [Setoid.Functions.Surjective][] module
we showed how to define a *decidable index type* in Agda. Here we use this to prove that the
projection of a product of algebras over such an index type is surjective.


```agda
module _  {I : Type ι}                  -- index type
           {_≟_ : Decidable{A = I} _≡_}  -- with decidable equality
           {𝒜 : I → Algebra {𝑆 = 𝑆} α ρ}         -- indexed collection of algebras
           {𝒜I : ∀ i → 𝕌[ 𝒜 i ] }        -- each of which is nonempty
           where

  ProjAlgIsOnto : ∀{i} → Σ[ h ∈ (𝕌[ ⨅ 𝒜 ] → 𝕌[ 𝒜 i ]) ] onto h
  ProjAlgIsOnto {i} = (proj _≟_ 𝒜I i) , projIsOnto _≟_ 𝒜I
```
