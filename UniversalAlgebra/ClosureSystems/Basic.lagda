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

open import Agda.Primitive             using    ( _⊔_   ;  Level
                                                ; lsuc            )
                                       renaming ( Set   to Type   )
open import Data.Empty.Polymorphic     using    ( ⊥ )
open import Data.Unit.Polymorphic      using    (⊤ ; tt)
open import Relation.Binary.Bundles    using    ( Poset           )
open import Relation.Unary             using    ( Pred  ;   _⊆_
                                                ; _∈_   ;   ⋂     )

open import ClosureSystems.Definitions using    ( Extensive ; OrderPreserving ; Idempotent )

-- universe-polymorphic emptyset type
∅ : {ℓ ℓ₁ : Level}{A : Type ℓ} → Pred A ℓ₁
∅ = λ _ → ⊥

-- closure system
data 𝒞𝓁 {ℓ : Level}(X : Type ℓ) : Pred (Pred X ℓ) (ℓ ⊔ lsuc ℓ) where
 nul : ∅ ∈ 𝒞𝓁 X
 all  : (λ _ → ⊤) ∈ 𝒞𝓁 X
 and : {I : Type}(c : I → Pred X ℓ) → (∀ i → c i ∈ 𝒞𝓁 X) → (⋂ I c) ∈ 𝒞𝓁 X

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

 field
  C : A → A
  isExtensive       : Extensive _≤_ C
  isOrderPreserving : OrderPreserving _≤_ C
  isIdempotent      : Idempotent _≈_ C

\end{code}




--------------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
