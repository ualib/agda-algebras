---
layout: default
title : Complexity.FiniteCSP module (The Agda Universal Algebra Library)
date : 2021-07-14
author: [agda-algebras development team][]
---

### Constraint Satisfaction Problems

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Complexity.FiniteCSP where

open import Agda.Primitive         using    ( _⊔_ ; lsuc ; Level)
                                   renaming ( Set to Type )
open import Data.Product           using    ( _,_ ; Σ ; Σ-syntax )
open import Data.Nat.Base          using    ( ℕ )
open import Data.Fin.Base          using    ( Fin )
open import Function.Base          using    ( _∘_ )
open import Relation.Unary         using    ( _∈_; Pred   )

open import Relations.Continuous   using    ( Rel )
open import Algebras.Basic         using    ( Signature )

\end{code}


#### Finite CSP

An instance of a (finite) constraint satisfaction problem is a triple 𝑃 = (𝑉, 𝐷, 𝐶) where

* 𝑉 is a finite set of variables,
* 𝐷 is a finite domain,
* 𝐶 is a finite list of constraints, where
  each constraint is a pair 𝐶 = (𝑥, 𝑅) in which
  * 𝑥 is a tuple of variables of length 𝑛, called the scope of 𝐶, and
  * 𝑅 is an 𝑛-ary relation on 𝐷, called the constraint relation of 𝐶.

\begin{code}

private variable χ ρ : Level

record Constraint (∣V∣ ∣D∣ : ℕ) : Type (lsuc (χ ⊔ ρ)) where
 field
  scope : Fin ∣V∣ → Type χ -- a subset of Fin ∣V∣

  relation : ((v : Fin ∣V∣ ) → v ∈ scope → Fin ∣D∣) → Type ρ
  -- a subset of "tuples" (i.e., functions 𝑓 : scope → Fin ∣D∣)

 -- An assignment 𝑓 : 𝑉 → 𝐷 of values in the domain to variables in 𝑉
 -- *satisfies* the constraint 𝐶 = (𝑥, 𝑅) if 𝑓 ↾ 𝑥 ∈ 𝑅.
 satisfies : (Fin ∣V∣ → Fin ∣D∣) → Type ρ
 satisfies f = (λ v _ → f v) ∈ relation


open Constraint

record CSPInstance : Type (lsuc (χ ⊔ ρ)) where
 field
  ∣V∣ -- # of variables,
   ∣D∣ -- # of elements in the domain,
    ∣C∣ -- # of constraints (resp.)
       : ℕ
  𝐶    : Fin ∣C∣ → Constraint{χ} ∣V∣ ∣D∣

 -- An assignment 𝑓 *solves* the instance 𝑃 if it satisfies all the constraints.
 isSolution : (Fin ∣V∣ → Fin ∣D∣) → Type ρ
 isSolution f = ∀ i → (satisfies (𝐶 i)) f

\end{code}



#### References

Some of the informal (i.e., non-agda) material in this module is similar to that presented in

* Ross Willard's slides: [Constraint Satisfaction Problems: a Survey](http://www.math.uwaterloo.ca/~rdwillar/documents/Slides/willard-boulder2016-rev2.pdf)

* [Polymorphisms, and How to Use Them](https://drops.dagstuhl.de/opus/volltexte/2017/6959/pdf/DFU-Vol7-15301-1.pdf



--------------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team


