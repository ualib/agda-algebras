---
layout: default
title : "ClosureSystems.Basic module (The Agda Universal Algebra Library)"
date : "2021-07-08"
author: "agda-algebras development team"
---

### <a id="basic-definitions">Basic definitions</a>

This is the [ClosureSystems.Basic][] module of the [Agda Universal Algebra Library][].

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

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module ClosureSystems.Basic where

-- Imports from Agda and the Agda Standard Library  ---------------------------------------
open import Agda.Primitive           using ( _⊔_ ; lsuc ) renaming ( Set to Type )
import Algebra.Definitions
open import Data.Product             using ( Σ-syntax )
open import Level                    using ( Level ; Lift ) renaming ( zero to ℓ₀ )
open import Relation.Binary.Bundles  using ( Poset )
open import Relation.Binary.Core     using ( Rel ; _Preserves_⟶_ )
open import Relation.Unary           using ( Pred ; _∈_ ; ⋂ )

private variable
 α ρ : Level
 a : Type α

Extensive : Rel a ρ → (a → a) → Type _
Extensive _≤_ C = ∀{x} → x ≤ C x

-- (We might propose a new stdlib equivalent to Extensive in, e.g., `Relation.Binary.Core`.)

module _ {χ ρ ℓ : Level}{X : Type χ} where

 IntersectClosed : Pred (Pred X ℓ) ρ → Type _
 IntersectClosed C = ∀ {I : Type ℓ}{c : I → Pred X ℓ} → (∀ i → (c i) ∈ C) → ⋂ I c ∈ C

 ClosureSystem : Type _
 ClosureSystem = Σ[ C ∈ Pred (Pred X ℓ) ρ ] IntersectClosed C

\end{code}


#### <a id="closure-operators">Closure Operators</a>

Let `𝑷 = (P, ≤)` be a poset. An function `C : P → P` is called a *closure operator*
on `𝑷` if it is

1. (extensive) `∀ x → x ≤ C x`
2. (order preserving) `∀ x y → x ≤ y → C x ≤ C y`
3. (idempotent) `∀ x → C (C x) = C x`

Thus, a closure operator is an extensive, idempotent poset endomorphism.

\begin{code}

-- ClOp, the inhabitants of which denote closure operators.
record ClOp {ℓ ℓ₁ ℓ₂ : Level}(𝑨 : Poset ℓ ℓ₁ ℓ₂) : Type  (ℓ ⊔ ℓ₂ ⊔ ℓ₁) where

 open Poset 𝑨
 private
   A = Carrier

 open Algebra.Definitions (_≈_)

 field
  C : A → A
  isExtensive       : Extensive _≤_ C
  isOrderPreserving : C Preserves _≤_ ⟶ _≤_
  isIdempotent      : IdempotentFun C

\end{code}

--------------------------------------

<span style="float:left;">[↑ ClosureSystems.Definitions](ClosureSystems.html)</span>
<span style="float:right;">[ClosureSystems.Properties →](ClosureSystems.Properties.html)</span>

{% include UALib.Links.md %}
