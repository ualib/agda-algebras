---
layout: default
title : "Overture.Adjunction.Closure module (The Agda Universal Algebra Library)"
date : "2026-05-09"
author: "the agda-algebras development team"
---

### Closure Systems and Operators

This is the [Overture.Adjunction.Closure][] module of the [Agda Universal Algebra Library][].

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Overture.Adjunction.Closure where

open import Agda.Primitive           using () renaming ( Set to Type )

-- Imports from the Agda Standard Library  ---------------------------------------
import Algebra.Definitions
open import Data.Product             using ( Σ-syntax ; _,_ ; _×_ )
open import Function                 using ( _∘₂_ )
open import Function.Bundles         using ( _↔_ ; Inverse)
open import Level                    using ( _⊔_ ; Level ) renaming ( suc to lsuc )
open import Relation.Binary.Bundles  using ( Poset )
open import Relation.Binary.Core     using ( Rel ; _Preserves_⟶_ )
open import Relation.Unary           using ( Pred ; _∈_ ; ⋂ )

import Relation.Binary.Reasoning.PartialOrder as ≤-Reasoning

private variable
 α ρ ℓ ℓ₁ ℓ₂ : Level
 a : Type α
```

#### Closure Systems

A *closure system* on a set `X` is a collection `𝓒` of subsets of `X` that is closed
under arbitrary intersection (including the empty intersection, so `⋂ ∅ = X ∈ 𝓒`).
Thus a closure system is a complete meet semilattice with respect to the subset
inclusion ordering.

Since every complete meet semilattice is automatically a complete lattice, the closed
sets of a closure system form a complete lattice.  (See Theorem 2.5 in J.B. Nation's
[Lattice Theory Notes](http://math.hawaii.edu/~jb/math618/Nation-LatticeTheory.pdf).)

Some examples of closure systems are the following:

+  order ideals of an ordered set
+  subalgebras of an algebra
+  equivalence relations on a set
+  congruence relations of an algebra

```agda
Extensive : Rel a ρ → (a → a) → Type _
Extensive _≤_ C = ∀{x} → x ≤ C x
-- (We might propose a new stdlib equivalent to Extensive in, e.g., `Relation.Binary.Core`.)

module _ {χ ρ ℓ : Level}{X : Type χ} where

 IntersectClosed : Pred (Pred X ℓ) ρ → Type (χ ⊔ ρ ⊔ lsuc ℓ)
 IntersectClosed C = ∀ {I : Type ℓ}{c : I → Pred X ℓ} → (∀ i → (c i) ∈ C) → ⋂ I c ∈ C

 ClosureSystem : Type _
 ClosureSystem = Σ[ C ∈ Pred (Pred X ℓ) ρ ] IntersectClosed C
```

#### Closure Operators

Let `𝑷 = (P, ≤)` be a poset.  A function `C : P → P` is called a *closure operator*
on `𝑷` if it is

1. (extensive) `∀ x → x ≤ C x`
2. (order preserving) `∀ x y → x ≤ y → C x ≤ C y`
3. (idempotent) `∀ x → C (C x) = C x`

Thus, a closure operator is an extensive, idempotent poset endomorphism.

```agda
-- ClOp, the inhabitants of which denote closure operators.
record ClOp {ℓ ℓ₁ ℓ₂ : Level}(𝑨 : Poset ℓ ℓ₁ ℓ₂) : Type  (ℓ ⊔ ℓ₂ ⊔ ℓ₁) where
 open Poset 𝑨 using (Carrier; _≈_; _≤_)
 open Algebra.Definitions (_≈_)
 field
  C                  : Carrier → Carrier
  isExtensive        : Extensive _≤_ C
  isOrderPreserving  : C Preserves _≤_ ⟶ _≤_
  isIdempotent       : IdempotentFun C
```

#### Basic properties of closure operators

```agda
module _ {𝑨 : Poset ℓ ℓ₁ ℓ₂}(𝑪 : ClOp 𝑨) where
  open Poset 𝑨 renaming (Carrier to A) using (_≤_)
  open ≤-Reasoning 𝑨
  open ClOp 𝑪
```

**Theorem 1**. If `𝑨 = (A , ≦)` is a poset and `C` is a closure operator on `A`, then

    ∀ (x y : A) → (x ≦ C y ↔ C x ≦ C y).

```agda
  clop→law⇒ : (x y : A) → x ≤ (C y) → (C x) ≤ (C y)
  clop→law⇒ x y x≤cy = begin
    C x      ≤⟨ isOrderPreserving x≤cy ⟩
    C (C y)  ≈⟨ isIdempotent y ⟩
    C y      ∎

  clop→law⇐ : (x y : A) → C x ≤ C y → x ≤ C y
  clop→law⇐ x y cx≤cy = begin
    x    ≤⟨ isExtensive ⟩
    C x  ≤⟨ cx≤cy ⟩
    C y  ∎
```

The converse of Theorem 1 also holds.  That is,

**Theorem 2**.  If `𝑨 = (A , ≤)` is a poset and `C : A → A` satisfies
`∀ (x y : A) → (x ≤ C y ↔ C x ≤ C y)`, then `C` is a closure operator on `A`.

```agda
module _ {𝑨 : Poset ℓ ℓ₁ ℓ₂} where
  open Poset 𝑨 renaming (Carrier to A) using (_≈_; _≤_; refl; trans; antisym)
  open Algebra.Definitions (_≈_)
  open Inverse using (from; to)

  clop←law :  (c : A → A) → ((x y : A) → (x ≤ c y ↔ c x ≤ c y))
    → Extensive _≤_ c × c Preserves _≤_ ⟶ _≤_ × IdempotentFun c

  clop←law c hyp  = e , (o , i)
    where
    e : Extensive _≤_ c
    e = (from ∘₂ hyp) _ _ refl

    o : c Preserves _≤_ ⟶ _≤_
    o u = (to ∘₂ hyp) _ _ (trans u e)

    i : IdempotentFun c
    i x = antisym ((to ∘₂ hyp) _ _ refl) ((from ∘₂ hyp) _ _ refl)
```
