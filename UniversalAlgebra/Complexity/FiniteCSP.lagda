---
layout: default
title : Complexity.FiniteCSP module (The Agda Universal Algebra Library)
date : 2021-07-26
author: [agda-algebras development team][]
---

### Constraint Satisfaction Problems

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Complexity.FiniteCSP  where

open import Agda.Builtin.Equality using ( _≡_ ; refl )
open import Data.Bool             using ( Bool ; true ; false ; _∧_)
open import Data.Fin.Base         using ( Fin ; toℕ ; fromℕ ; raise)
open import Data.Vec              using ( Vec ; [] ; tabulate ; lookup ; _∷_ ; map )
open import Data.Vec.Relation.Unary.All using ( All )
open import Data.Nat              using ( ℕ ; zero ; suc ; _+_ )

open import Agda.Primitive   using ( _⊔_ ; lsuc ; Level) renaming ( Set to Type )
open import Function.Base    using ( _∘_ )
open import Relation.Binary  using ( DecSetoid)

private variable
 α ℓ : Level

\end{code}

#### Constraints

We start with a vector (of length n, say) of variables.  For simplicity, we'll use the natural
numbers for variable symbols, so

V : Vec ℕ n
V = [0 1 2 ... n-1]

We can use the following range function to construct the vector of variables.

\begin{code}

range : (n : ℕ) → Vec ℕ n
range n = tabulate toℕ
-- `range n` is 0 ∷ 1 ∷ 2 ∷ … ∷ n-1 ∷ []

\end{code}

Let `nvar` denote the number of variables.

A *constraint* consists of

1. a natural number `∣s∣` denoting the number of variables in the "scope" of the constraint;

2. a scope vector,  `s : Vec (Fin nvar) ∣s∣` , where `s i` is `k` if `k` is the i-th variable
   in the scope of the constraint.

3. a constraint relation, rel, which is a collection of functions mapping (indices of)
   variables in the scope to elements of the domain.

To summarize, a constraint is a triple (∣s∣ , s , rel), where
* ∣s∣ is the number of variables in scope s.
* s is the scope function: s i ≡ v iff v is the i-th variable in scope s.
* rel is the contraint relation: a collection of functions mapping indices
  of scope variables to elements in the domain.

\begin{code}

open DecSetoid
open Fin renaming (zero to fzer ; suc to fsuc)

record Constraint (nvar : ℕ) (dom : Vec (DecSetoid α ℓ) nvar) : Type α where
 field
  ∣s∣ : Fin nvar                     -- The "number" of variables involved in the constraint.
  s : Vec (Fin nvar) (toℕ ∣s∣)        -- Vec of variables involved in the constraint.
  rel : ((i : Fin (toℕ ∣s∣)) → Carrier ((lookup dom) (lookup s i))) →  Bool
         -- `rel f` returns true iff the function f belongs to the relation

 satisfies : (∀ i → Carrier ((lookup dom) i)) → Bool         -- An assignment f of values to variables
 satisfies f = rel (λ (i : Fin (toℕ ∣s∣)) → f (lookup s i))  -- *satisfies* the constraint provided
                                                             -- the function f, evaluated at each variable
                                                             -- in the scope, belongs to the relation rel.


-- utility functions --
foldleft : ∀ {α β} {A : Type α} {B : Type β} {m} →
           (B → A → B) → B → Vec A m → B
foldleft _⊕_ b []       = b
foldleft _⊕_ b (x ∷ xs) = foldleft _⊕_ (b ⊕ x) xs
-- cf. stdlib's foldl, which seems harder to use than this one

bool2nat : Bool → ℕ
bool2nat false = 0
bool2nat true = 1

-- The number of elements of v that satisfy P
countBool : {n : ℕ}{A : Set α} → Vec A n → (P : A → Bool) → ℕ
countBool v P = foldleft _+_ 0 (map (bool2nat ∘ P) v)
-- cf. stdlib's count, which works with general predicates (of type Pred A _)

-- Return true iff all elements of v satisfy predicate P
AllBool : ∀{n}{A : Set α} → Vec A n → (P : A → Bool) → Bool
AllBool v P = foldleft _∧_ true (map P v)
-- cf. stdlib's All, which works with general predicates (of type Pred A _)



open Constraint
record CSPInstance (nvar : ℕ) (dom : Vec (DecSetoid α ℓ) nvar) : Type α where
 field
  ncon : ℕ      -- the number of constraints involved
  constr : Vec (Constraint nvar dom) ncon

 -- f *solves* the instance if it satisfies all constraints.
 isSolution :  (∀ i → Carrier ((lookup dom) i)) → Bool
 isSolution f = AllBool constr P
  where
  P : Constraint nvar dom → Bool
  P c = (satisfies c) f

 -- A more general version...? (P is a more general Pred)
 isSolution' :  (∀ i → Carrier ((lookup dom) i)) → Type α
 isSolution' f = All P constr
  where
  P : Constraint nvar dom → Type
  P c = (satisfies c) f ≡ true


\end{code}



--------------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team


