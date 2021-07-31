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

open import Agda.Primitive        using ( _⊔_ ; lsuc ; Level) renaming ( Set to Type )
open import Agda.Builtin.List     using (List; []; _∷_)
open import Data.Bool             using ( Bool ; T? ; true)
open import Data.Bool.Base        using ( T ; _∧_ )
open import Data.Fin.Base         using ( Fin ; toℕ )
open import Data.List.Base        using ( length ; [_] ; _++_; head ; tail ; all) renaming (lookup to get)
open import Data.Product          using ( _,_ ; Σ-syntax ; _×_ )
open import Data.Vec              using ( Vec ; lookup ; count ; tabulate )
open import Data.Vec.Relation.Unary.All using ( All )
open import Data.Nat              using ( ℕ )
open import Function.Base         using ( _∘_ )
open import Relation.Binary       using ( DecSetoid ; Rel )
open import Relation.Nullary      using ( Dec )
open import Relation.Unary        using ( Pred ; _∈_ ; Decidable )

private variable
 α ℓ ρ : Level

\end{code}


#### Constraints

We start with a vector (of length n, say) of variables.  For simplicity, we'll use the natural
numbers for variable symbols, so

V : Vec ℕ n
V = [0 1 2 ... n-1]

We can use the following function to construct the vector of variables.

\begin{code}

range : (n : ℕ) → Vec ℕ n
range n = tabulate toℕ
-- `range n` is 0 ∷ 1 ∷ 2 ∷ … ∷ n-1 ∷ []

\end{code}

Let `nvar` denote the number of variables.

A *constraint* consists of

1. a scope vector,  `s : Vec Bool nvar` , where `s i` is `true` if variable `i` is in the scope
   of the constraint.

2. a constraint relation, rel, which is a collection of functions mapping
   variables in the scope to elements of the domain.

\begin{code}

-- syntactic sugar for vector element lookup
_⟨_⟩ : {A : Set α}{n : ℕ} → Vec A n → Fin n → A
v ⟨ i ⟩ = (lookup v) i


open DecSetoid

-- {nvar : ℕ}{dom : Vec (DecSetoid α ℓ) nvar} → 

open Dec

record Constraint {ρ : Level} (nvar : ℕ) (dom : Vec (DecSetoid α ℓ) nvar) : Type (α ⊔ lsuc ρ) where
 field
  s   : Vec Bool nvar        -- entry i is true iff variable i is in scope
  rel : Pred (∀ i → Carrier (dom ⟨ i ⟩)) ρ -- some functions from `Fin nvar` to `dom`
  dec : Decidable rel

 -- scope size (i.e., # of vars involved in constraint)
 ∣s∣ : ℕ
 ∣s∣ = count T? s

 -- point-wise equality of functions when restricted to the scope
 _≐s_ : Rel (∀ i → Carrier (dom ⟨ i ⟩)) ℓ
 f ≐s g = ∀ i → T (s ⟨ i ⟩) → (dom ⟨ i ⟩)._≈_ (f i) (g i)

 satisfies : (∀ i → Carrier (dom ⟨ i ⟩)) → Type (α ⊔ ℓ ⊔ ρ) -- An assignment f of values to variables
 satisfies f = Σ[ g ∈ (∀ i → Carrier (dom ⟨ i ⟩)) ]         -- *satisfies* the constraint provided
                ( (g ∈ rel) × f ≐s g )                        -- the function f, evaluated at each variable
                                                             -- in the scope, belongs to the relation rel.

 satisfies? : (f : ∀ i → Carrier (dom ⟨ i ⟩)) → Dec (satisfies f) -- Type (α ⊔ ℓ ⊔ ρ)
 satisfies? f = {!!}

open Constraint

record CSPInstance {ρ : Level} (nvar : ℕ) (dom : Vec (DecSetoid α ℓ) nvar) : Type (α ⊔ lsuc ρ)  where
 field
  ncon : ℕ      -- the number of constraints involved
  constr : Vec (Constraint {ρ = ρ} nvar dom) ncon

 -- f *solves* the instance if it satisfies all constraints.
 isSolution :  (∀ i → Carrier (dom ⟨ i ⟩)) → Type _
 isSolution f = All P constr
  where
  P : Pred (Constraint nvar dom) _
  P c = (satisfies c) f


record CSPInstanceList {ρ : Level}
                       (nvar : ℕ)
                       (dom : Vec (DecSetoid α ℓ) nvar) : Type (α ⊔ lsuc ρ)  where
 field
  constr : List (Constraint {ρ = ρ} nvar dom)

 -- f *solves* the instance if it satisfies all constraints.
 isSolution :  (∀ i → Carrier (dom ⟨ i ⟩)) → Bool
 isSolution f = all P constr
  where
  P : (Constraint nvar dom) → Bool
  P c = does ((satisfies? c) f) -- (satisfies c) f → 


\end{code}



Here's Jacques' nice explanation, comparing/contrasting a general predicate with a Bool-valued function:

"A predicate maps to a whole type's worth of evidence that the predicate holds (or none
at all if it doesn't). true just says it holds and absolutely nothing else. Bool is slightly
different though, because a Bool-valued function is equivalent to a proof-irrelevant
decidable predicate."












--------------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team























-- Return true iff all elements of v satisfy predicate P
-- AllBool : ∀{n}{A : Set α} → Vec A n → (P : A → Bool) → Bool
-- AllBool v P = foldleft _∧_ true (map P v)
-- cf. stdlib's All, which works with general predicates (of type Pred A _)


 -- A more general version...? (P is a more general Pred)
 -- isSolution' :  (∀ i → Carrier ((lookup dom) i)) → Type α
 -- isSolution' f = All P constr
 --  where
 --  P : Constraint nvar dom → Type
 --  P c = (satisfies c) f ≡ true

-- bool2nat : Bool → ℕ
-- bool2nat false = 0
-- bool2nat true = 1


-- The number of elements of v that satisfy P
-- countBool : {n : ℕ}{A : Set α} → Vec A n → (P : A → Bool) → ℕ
-- countBool v P = foldl (λ _ → ℕ) _+_ 0 (map (bool2nat ∘ P) v)

