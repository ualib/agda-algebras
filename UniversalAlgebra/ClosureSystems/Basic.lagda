---
layout: default
title : ClosureSystems.Basic module (The Agda Universal Algebra Library)
date : 2021-07-08
author: [agda-algebras development team][]
---

### Closure Systems and Operators

#### Closure Systems

A *closure system* on a set `X` is a collection `𝒞` of subsets of `X` that is closed
under arbitrary intersection (including the empty intersection, so `⋂ ∅ = X ∈ 𝒞`.

Thus a closure system is a complete meet semilattice with respect to the subset
inclusion ordering.

Since every complete meet semilattice is automatically a complete lattice, the closed
sets of a closure system form a complete lattice.
(See J.B. Nation's [Lattice Theory Notes](http://math.hawaii.edu/~jb/math618/Nation-LatticeTheory.pdf).)
\cite[Theorem 2.5]{Nation-notes}

Some examples of closure systems are the following:

* order ideals of an ordered set
* subalgebras of an algebra
* equivalence relations on a set
* congruence relations of an algebra


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module ClosureSystems.Basic where

open import Agda.Primitive           using ( _⊔_ ; lsuc )     renaming ( Set to Type )
import Algebra.Definitions
open import Data.Product             using ( Σ-syntax )
open import Level                    using ( Level ; Lift )   renaming ( zero to ℓ₀ )
open import Relation.Binary.Bundles  using ( Poset )
open import Relation.Binary.Core     using ( _Preserves_⟶_ )
open import Relation.Unary           using ( Pred ; _∈_ ; ⋂ )

open import ClosureSystems.Definitions using ( Extensive )


module _ {χ ℓ ρ ι : Level}{X : Type χ} where

 IntersectClosed : Pred (Pred X (ℓ ⊔ ι) ) ρ → Type _
 IntersectClosed C = ∀ {I : Type ι}{c : I → Pred X ℓ} → (∀ i → (λ x → Lift ι (c i x)) ∈ C) → ⋂ I c ∈ C

 ClosureSystem : Type _
 ClosureSystem = Σ[ C ∈ Pred (Pred X (ℓ ⊔ ι) ) ρ ] IntersectClosed C

\end{code}


#### Closure Operators

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

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
