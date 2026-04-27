---
layout: default
title : "Base.Algebras.Products module (Agda Universal Algebra Library)"
date : "2021-01-12"
author: "agda-algebras development team"
---

### <a id="products-of-algebras-and-product-algebras">Products of Algebras and Product Algebras</a>

This is the [Base.Algebras.Products][] module of the [Agda Universal Algebra Library][].


```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Base.Algebras.Products {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ------------------------------
open import Agda.Primitive  using () renaming ( Set to Type )
open import Data.Product    using ( _,_ ; Σ ; Σ-syntax )
open import Level           using ( Level ; _⊔_ ; suc )
open import Relation.Unary  using ( Pred ; _⊆_ ; _∈_ )

-- Imports from agda-algebras ---------------------------------------------------
open import Overture                     using (_⁻¹; 𝑖𝑑; ∣_∣; ∥_∥)
open import Base.Algebras.Basic {𝑆 = 𝑆}  using ( Algebra ; _̂_ ; algebra )

private variable α β ρ 𝓘 : Level
```


From now on, the modules of the
[agda-algebras](https://github.com/ualib/agda-algebras) library will assume a
fixed signature `𝑆 : Signature 𝓞 𝓥`.

Recall the informal definition of a *product* of `𝑆`-algebras. Given a type `I :
Type 𝓘` and a family `𝒜 : I → Algebra α`, the *product* `⨅ 𝒜` is the algebra
whose domain is the Cartesian product `Π 𝑖 ꞉ I , ∣ 𝒜 𝑖 ∣` of the domains of the
algebras in `𝒜`, and whose operations are defined as follows: if `𝑓` is a `J`-ary
operation symbol and if `𝑎 : Π 𝑖 ꞉ I , J → 𝒜 𝑖` is an `I`-tuple of `J`-tuples such
that `𝑎 𝑖` is a `J`-tuple of elements of `𝒜 𝑖` (for each `𝑖`), then `(𝑓 ̂ ⨅ 𝒜) 𝑎 :=
(i : I) → (𝑓 ̂ 𝒜 i)(𝑎 i)`.

In the [agda-algebras](https://github.com/ualib/agda-algebras) library a *product
of* `𝑆`-*algebras* is represented by the following type.


```agda


⨅ : {I : Type 𝓘 }(𝒜 : I → Algebra α ) → Algebra (𝓘 ⊔ α)

⨅ {I = I} 𝒜 =  ( ∀ (i : I) → ∣ 𝒜 i ∣ ) ,        -- domain of the product algebra
                λ 𝑓 𝑎 i → (𝑓 ̂ 𝒜 i) λ x → 𝑎 x i  -- basic operations of the product algebra
```


The type just defined is the one that will be used throughout the
[agda-algebras](https://github.com/ualib/agda-algebras) library whenever the
product of an indexed collection of algebras (of type `Algebra`) is required.
However, for the sake of completeness, here is how one could define a type
representing the product of algebras inhabiting the record type `algebra`. 


```agda


open algebra

⨅' : {I : Type 𝓘 }(𝒜 : I → algebra α) → algebra (𝓘 ⊔ α)
⨅' {I} 𝒜 = record  { carrier = ∀ i → carrier (𝒜 i)                         -- domain
                    ; opsymbol = λ 𝑓 𝑎 i → (opsymbol (𝒜 i)) 𝑓 λ x → 𝑎 x i }  -- basic operations
```


**Notation**. Given a signature `𝑆 : Signature 𝓞 𝓥`, the type `Algebra α` has
type `Type(𝓞 ⊔ 𝓥 ⊔ lsuc α)`.  Such types occur so often in the
[agda-algebras](https://github.com/ualib/agda-algebras) library that we define
the following shorthand for their universes.


```agda


ov : Level → Level
ov α = 𝓞 ⊔ 𝓥 ⊔ suc α
```



### <a id="products-of-classes-of-algebras">Products of classes of algebras</a>

An arbitrary class `𝒦` of algebras is represented as a predicate over the type
`Algebra α`, for some universe level `α` and signature `𝑆`. That is, `𝒦 : Pred
(Algebra α) β`, for some type `β`. Later we will formally state and prove that
the product of all subalgebras of algebras in `𝒦` belongs to the class `SP(𝒦)` of
subalgebras of products of algebras in `𝒦`. That is, `⨅ S(𝒦) ∈ SP(𝒦 )`. This turns
out to be a nontrivial exercise.

To begin, we need to define types that represent products over arbitrary
(nonindexed) families such as `𝒦` or `S(𝒦)`. Observe that `Π 𝒦` is certainly not
what we want.  For recall that `Pred (Algebra α) β` is just an alias for the
function type `Algebra α → Type β`, and the semantics of the latter takes `𝒦 𝑨`
(and `𝑨 ∈ 𝒦`) to mean that `𝑨` belongs to the class `𝒦`. Thus, by definition,

    Π 𝒦   :=   Π 𝑨 ꞉ (Algebra α) , 𝒦 𝑨   :=   ∀ (𝑨 : Algebra α) → 𝑨 ∈ 𝒦,

which asserts that every inhabitant of the type `Algebra α` belongs to `𝒦`.
Evidently this is not the product algebra that we seek.

What we need is a type that serves to index the class `𝒦`, and a function `𝔄` that
maps an index to the inhabitant of `𝒦` at that index. But `𝒦` is a predicate (of
type `(Algebra α) → Type β`) and the type `Algebra α` seems rather nebulous in
that there is no natural indexing class with which to "enumerate" all inhabitants
of `Algebra α` belonging to `𝒦`.

The solution is to essentially take `𝒦` itself to be the indexing type, at least
heuristically that is how one can view the type `ℑ` that we now define.


```agda


module _ {𝒦 : Pred (Algebra α)(ov α)} where
 ℑ : Type (ov α)
 ℑ = Σ[ 𝑨 ∈ Algebra α ] 𝑨 ∈ 𝒦
```


Taking the product over the index type `ℑ` requires a function that maps an index
`i : ℑ` to the corresponding algebra.  Each `i : ℑ` is a pair, `(𝑨 , p)`, where
`𝑨` is an algebra and `p` is a proof that `𝑨` belongs to `𝒦`, so the function
mapping an index to the corresponding algebra is simply the first projection.


```agda


 𝔄 : ℑ → Algebra α
 𝔄 i = ∣ i ∣
```


Finally, we define `class-product` which represents the product of all members of
𝒦.


```agda


 class-product : Algebra (ov α)
 class-product = ⨅ 𝔄
```


If `p : 𝑨 ∈ 𝒦`, we view the pair `(𝑨 , p) ∈ ℑ` as an *index* over the class, so we
can think of `𝔄 (𝑨 , p)` (which is simply `𝑨`) as the projection of the product `⨅
𝔄` onto the `(𝑨 , p)`-th component.

-----------------------

<span style="float:left;">[← Base.Algebras.Basic](Base.Algebras.Basic.html)</span>
<span style="float:right;">[Base.Algebras.Congruences →](Base.Algebras.Congruences.html)</span>

{% include UALib.Links.md %}
