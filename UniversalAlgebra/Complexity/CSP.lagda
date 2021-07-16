---
layout: default
title : Complexity.CSP module (The Agda Universal Algebra Library)
date : 2021-07-14
author: [agda-algebras development team][]
---

### Constraint Satisfaction Problems

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Complexity.CSP {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive   using ( _⊔_ ; lsuc ; Level) renaming ( Set to Type )
open import Function.Base    using ( _∘_ )
open import Relation.Binary  using ( Setoid )


open import Relations.Continuous    using ( ΠΡ ; ΠΡ-syntax )
open import Algebras.Setoid {𝑆 = 𝑆} using ( SetoidAlgebra )


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
         {α ℓ : Level} -- ... domain types
         where
 open Setoid
 record Constraint (var : Type ν) (dom : var → Setoid α ℓ) : Type (ν ⊔ α ⊔ lsuc ι) where
  field
   arity  : Type ι               -- The "number" of variables involved in the constraint.
   scope  : arity → var          -- Which variables are involved in the constraint.
   rel    : ΠΡ[ i ∈ arity ] (Carrier (dom (scope i)))     -- The constraint relation.

  satisfies : (∀ v → Carrier (dom v)) → Type  -- An assignment 𝑓 : var → dom of values to variables
  satisfies f = rel (f ∘ scope)      -- *satisfies* the constraint 𝐶 = (σ , 𝑅) provided
                                    -- 𝑓 ∘ σ ∈ 𝑅, where σ is the scope of the constraint.
\end{code}

#### CSP Templates and Instances

A CSP "template" restricts the relations that may occur in instances of the problem.
A convenient way to specify a template is to give an indexed family
𝒜 : var → SetoidAlgebra α ρ of algebras (one for each variable symbol in var)
and require that relations be subalgebras of the product ⨅ var 𝒜.

To construct a CSP instance, then, we just have to give a family 𝒜 of algebras, specify
the number (ar) of constraints, and for each i : ar, define a constraint as a relation
over (some of) the members of 𝒜.

An instance of a constraint satisfaction problem is a triple 𝑃 = (𝑉, 𝐷, 𝐶) where

* 𝑉 denotes a set of "variables"
* 𝐷 denotes a "domain",
* 𝐶 denotes an indexed collection of constraints.

\begin{code}
 open SetoidAlgebra
 open Setoid
 record CSPInstance (var : Type ν)(𝒜 : var → SetoidAlgebra α ℓ) : Type (ν ⊔ α ⊔ lsuc ι) where
  field
   ar : Type ι       -- ar indexes the contraints in the instance
   cs : (i : ar) → Constraint var (λ v → Domain (𝒜 v))

  isSolution : (∀ v → Carrier (Domain (𝒜 v))) → Type _  -- An assignment *solves* the instance
  isSolution f = ∀ i → (Constraint.satisfies (cs i)) f  -- if it satisfies all the constraints.

\end{code}



--------------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team


