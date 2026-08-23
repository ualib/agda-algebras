---
layout: default
title : "Setoid.Algebras.Products module (Agda Universal Algebra Library)"
date : "2021-07-03"
author: "agda-algebras development team"
---

#### Products of Setoid Algebras

This is the [Setoid.Algebras.Products][] module of the [Agda Universal Algebra Library][].

The **product** of an indexed family of algebras is formed coordinatewise: its carrier is the dependent function type over the index, its equality is pointwise, and each operation symbol is interpreted by applying the corresponding operation in every factor.  This module defines that product, `⨅`{.AgdaFunction}; the machinery for taking the product of a *class* of algebras rather than of an indexed family; and the one nontrivial fact about products proved here, that the coordinate projections out of a product are surjective when the index type has decidable equality and every factor is nonempty.

Products are one of the three closure operations `H`, `S`, `P` whose composite `V` defines a variety, so this module is used throughout [Setoid.Varieties.Closure][] and in the proof of Birkhoff's theorem in [Setoid.Varieties.HSP][].  Homomorphisms into and out of a product are in [Setoid.Homomorphisms.Products][], and `⨅≅`{.AgdaFunction} of [Setoid.Homomorphisms.Isomorphisms][] shows that products of isomorphic families are isomorphic.

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

`⨅ 𝒜`{.AgdaFunction} is the **product** of the family `𝒜 : I → Algebra α ρ`.  Its carrier is the dependent product `∀ i → 𝕌[ 𝒜 i ]` of the carriers of the factors; two elements are equal exactly when they agree in every coordinate; and the interpretation of an operation symbol `f` is the tuple of interpretations of `f` in the factors, `(f ^ ⨅ 𝒜) a i = (f ^ 𝒜 i) (flip a i)`.  Reflexivity, symmetry and transitivity are inherited coordinatewise, and so is the congruence proof for `Interp`{.AgdaField}.

Both levels of the result absorb the level `ι` of the index type, since the carrier is a function out of `I` and the equality is an `I`-indexed conjunction.  A product therefore sits at the join of its factors' levels with the level of its index, and correspondingly `P`{.AgdaFunction} of [Setoid.Varieties.Closure][] states membership up to isomorphism, as `𝑩 ≅ ⨅ 𝒜`, which leaves `𝑩` its own pair of levels.

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

A class of algebras is given as a predicate `𝒦 : Pred (Algebra α ρ) _`, not as an indexed family, so `⨅`{.AgdaFunction} cannot be applied to it directly; and the dependent product over the predicate is not what is wanted either, since `∀ 𝑨 → 𝑨 ∈ 𝒦` asserts that *every* algebra belongs to `𝒦`.  The remedy is to take the class itself as the index: `ℑ`{.AgdaFunction} is the type of pairs `(𝑨 , p)` with `p : 𝑨 ∈ 𝒦`, `𝔄`{.AgdaFunction} sends such a pair to its first component, and `class-product`{.AgdaFunction} is `⨅ 𝔄`, the product of all the members of `𝒦`.

Indexing by proofs rather than by algebras means that an algebra carrying two membership proofs contributes two identical factors; the result is a product of members of `𝒦` regardless.  The variant that indexes by an environment as well appears as `ℑ⁺`, `𝔄⁺` and `ℭ` in [Setoid.Varieties.HSP][].

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
