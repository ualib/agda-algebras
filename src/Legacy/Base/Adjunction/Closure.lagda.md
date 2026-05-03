---
layout: default
title : "Base.Adjunction.Closure module (The Agda Universal Algebra Library)"
date : "2021-08-30"
author: "agda-algebras development team"
---

### <a id="closure-systems">Closure Systems and Operators</a>

This is the [Base.Adjunction.Closure][] module of the [Agda Universal Algebra Library][].


```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Legacy.Base.Adjunction.Closure where

-- Imports from Agda and the Agda Standard Library  ---------------------------------------
open import Agda.Primitive           using () renaming ( Set to Type )
import Algebra.Definitions
open import Data.Product             using ( Σ-syntax ; _,_ ; _×_ )
open import Function                 using ( _∘₂_ )
open import Function.Bundles         using ( _↔_ ; Inverse)
open import Level                    using ( _⊔_ ; Level )
open import Relation.Binary.Bundles  using ( Poset )
open import Relation.Binary.Core     using ( Rel ; _Preserves_⟶_ )
open import Relation.Unary           using ( Pred ; _∈_ ; ⋂ )

import Relation.Binary.Reasoning.PartialOrder as ≤-Reasoning

private variable
 α ρ ℓ ℓ₁ ℓ₂ : Level
 a : Type α
```


#### <a id="closure-systems">Closure Systems</a>

A *closure system* on a set `X` is a collection `𝒞` of subsets of `X` that is closed
under arbitrary intersection (including the empty intersection, so `⋂ ∅ = X ∈ 𝒞`.
Thus a closure system is a complete meet semilattice with respect to the subset
inclusion ordering.

Since every complete meet semilattice is automatically a complete lattice, the closed
sets of a closure system form a complete lattice.
(See J.B. Nation's [Lattice Theory Notes](http://math.hawaii.edu/~jb/math618/Nation-LatticeTheory.pdf), Theorem 2.5.)

Some examples of closure systems are the following:

* order ideals of an ordered set
* subalgebras of an algebra
* equivalence relations on a set
* congruence relations of an algebra


```agda


Extensive : Rel a ρ → (a → a) → Type _
Extensive _≤_ C = ∀{x} → x ≤ C x
-- (We might propose a new stdlib equivalent to Extensive in, e.g., `Relation.Binary.Core`.)

module _ {χ ρ ℓ : Level}{X : Type χ} where

 IntersectClosed : Pred (Pred X ℓ) ρ → Type _
 IntersectClosed C = ∀ {I : Type ℓ}{c : I → Pred X ℓ} → (∀ i → (c i) ∈ C) → ⋂ I c ∈ C

 ClosureSystem : Type _
 ClosureSystem = Σ[ C ∈ Pred (Pred X ℓ) ρ ] IntersectClosed C
```



#### <a id="closure-operators">Closure Operators</a>

Let `𝑷 = (P, ≤)` be a poset. An function `C : P → P` is called a *closure operator*
on `𝑷` if it is

1. (extensive) `∀ x → x ≤ C x`
2. (order preserving) `∀ x y → x ≤ y → C x ≤ C y`
3. (idempotent) `∀ x → C (C x) = C x`

Thus, a closure operator is an extensive, idempotent poset endomorphism.


```agda


-- ClOp, the inhabitants of which denote closure operators.
record ClOp {ℓ ℓ₁ ℓ₂ : Level}(𝑨 : Poset ℓ ℓ₁ ℓ₂) : Type  (ℓ ⊔ ℓ₂ ⊔ ℓ₁) where
 open Poset 𝑨
 private A = Carrier
 open Algebra.Definitions (_≈_)
 field
  C : A → A
  isExtensive        : Extensive _≤_ C
  isOrderPreserving  : C Preserves _≤_ ⟶ _≤_
  isIdempotent       : IdempotentFun C
```



#### <a id="basic-properties-of-closure-operators">Basic properties of closure operators</a>


```agda


open ClOp
open Inverse

module _ {𝑨 : Poset ℓ ℓ₁ ℓ₂}(𝑪 : ClOp 𝑨) where
 open Poset 𝑨
 open ≤-Reasoning 𝑨
 private
  c = C 𝑪
  A = Carrier
```


**Theorem 1**. If `𝑨 = (A , ≦)` is a poset and `c` is a closure operator on `A`, then
               `∀ (x y : A) → (x ≦ (c y) ↔ (c x) ≦ (c y))`


```agda


 clop→law⇒ : (x y : A) → x ≤ (c y) → (c x) ≤ (c y)
 clop→law⇒ x y x≤cy = begin
   c x      ≤⟨ isOrderPreserving 𝑪 x≤cy ⟩
   c (c y)  ≈⟨ isIdempotent 𝑪 y ⟩
   c y      ∎

 clop→law⇐ : (x y : A) → (c x) ≤ (c y) → x ≤ (c y)
 clop→law⇐ x y cx≤cy = begin
   x    ≤⟨ isExtensive 𝑪 ⟩
   c x  ≤⟨ cx≤cy ⟩
   c y  ∎
```


The converse of Theorem 1 also holds. That is,

**Theorem 2**. If `𝑨 = (A , ≤)` is a poset and `c : A → A` satisfies
               `∀ (x y : A) → (x ≤ (c y) ↔ (c x) ≤ (c y))`

               then `c` is a closure operator on `A`.


```agda


module _ {𝑨 : Poset ℓ ℓ₁ ℓ₂} where
 open Poset 𝑨
 private A = Carrier
 open Algebra.Definitions (_≈_)

 clop←law :  (c : A → A) → ((x y : A) → (x ≤ (c y) ↔ (c x) ≤ (c y)))
  →          Extensive _≤_ c × c Preserves _≤_ ⟶ _≤_ × IdempotentFun c

 clop←law c hyp  = e , (o , i)
  where
  e : Extensive _≤_ c
  e = (from ∘₂ hyp) _ _ refl

  o : c Preserves _≤_ ⟶ _≤_
  o u = (to ∘₂ hyp) _ _ (trans u e)

  i : IdempotentFun c
  i x = antisym ((to ∘₂ hyp) _ _ refl) ((from ∘₂ hyp) _ _ refl)
```


----------------------------

<span style="float:left;">[↑ Base.Adjunction](Base.Adjunction.html)</span>
<span style="float:right;">[Base.Adjunction.Galois →](Base.Adjunction.Galois.html)</span>

{% include UALib.Links.md %}
