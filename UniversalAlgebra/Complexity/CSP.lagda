---
layout: default
title : Complexity.CSP module (The Agda Universal Algebra Library)
date : 2021-07-14
author: [agda-algebras development team][]
---

### Constraint Satisfaction Problems

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Complexity.CSP where

open import Agda.Primitive         using    ( _⊔_ ; lsuc ; Level)
                                   renaming ( Set to Type )
open import Function.Base          using    ( _∘_ )
open import Relation.Unary         using    ( _∈_; Pred   )

open import Relations.Continuous   using    ( Rel )

\end{code}

#### Constraints

A constraint c consists of

 1. a scope function,  s : I → var, and

 2. a constraint relation, i.e., a predicate over the function type I → D

        I ···> var
         .     .
          .   .
           ⌟ ⌞
            D


The *scope* of a constraint is an indexed subset of the set of variable symbols.
We could define a type for this, e.g.,

```
 Scope : Type ν → Type ι → _
 Scope V I = I → V
```

but we omit this definition because it's so simple; to reiterate,
a scope of "arity" I on "variables" V is simply a map from I to V,
where,

* I denotes the "number" of variables involved in the scope
* V denotes a collection (type) of "variable symbols"

\begin{code}

module _ -- levels for...
         {ι : Level} -- ...arity (or argument index) types
         {ν : Level} -- ...variable symbol types
         {δ : Level} -- ... domain types
         -- {ρ : Level} -- ... relation types
         where

 record Constraint (var : Type ν)(dom : Type δ){ρ : Level} : Type (ν ⊔ δ ⊔ lsuc (ι ⊔ ρ)) where
  field
   arity  : Type ι               -- The "number" of variables involved in the constraint.
   scope  : arity → var          -- Which variables are involved in the constraint.
   rel    : Rel dom arity {ρ}    -- The constraint relation.

  satisfies : (var → dom) → Type ρ  -- An assignment 𝑓 : var → dom of values to variables
  satisfies f = f ∘ scope ∈ rel     -- *satisfies* the constraint 𝐶 = (σ , 𝑅) provided
                                    -- 𝑓 ∘ σ ∈ 𝑅, where σ is the scope of the constraint.

\end{code}

#### CSP Instances

An instance of a constraint satisfaction problem is a triple 𝑃 = (𝑉, 𝐷, 𝐶) where

* 𝑉 denotes a set of "variables"
* 𝐷 denotes a "domain",
* 𝐶 denotes an indexed collection of constraints.

\begin{code}

 record CSPInstance  (var : Type ν)(dom : Type δ){ρ : Level} : Type (ν ⊔ δ ⊔ lsuc (ι ⊔ ρ)) where
  field
   arity : Type ι                         -- The "number" of constraints of the instance.
   cs    : arity → Constraint var dom {ρ} -- The constraints of the instance.

  isSolution : (var → dom) → Type (ι ⊔ ρ)               -- An assignment *solves* the instance
  isSolution f = ∀ i → (Constraint.satisfies (cs i)) f  -- if it satisfies all the constraints.

\end{code}



--------------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team


