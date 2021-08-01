n---
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
open import Data.Fin.Base         using ( Fin ; toℕ ; fold′ ; fromℕ ; raise )
open import Data.List.Base        using ( [_] ; _++_; head ; tail ; all) renaming (lookup to get)
open import Data.Product          using ( _,_ ; Σ-syntax ; _×_ ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Data.Vec              using ( Vec ; lookup ; filter ; zip )
open import Data.Vec.Base         using ( allFin ; count ; tabulate ) renaming (length to vlength)
open import Data.Vec.Bounded.Base using ( Vec≤ )
open import Data.Vec.Relation.Unary.All using ( All )
open import Data.Nat              using ( ℕ ; zero ; suc )
open import Function.Base         using ( _∘_ )
open import Relation.Binary       using ( DecSetoid ; Rel )
open import Relation.Binary.Structures using ( IsDecEquivalence )
open import Relation.Nullary      using ( Dec ; _because_ ; Reflects )
open import Relation.Unary        using ( Pred ; _∈_ ; Decidable ; ⋂ )

open import Overture.Preliminaries using ( Π-syntax )


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

module finite-csp
 {ρ : Level}
 (nvar' : ℕ)
 (dom : Vec (DecSetoid α ℓ) (suc nvar')) where

 private
  nvar = suc nvar'

 open Vec≤

 record Constraint : Type (α ⊔ lsuc ρ) where
  field
   s   : Vec Bool nvar        -- entry i is true iff variable i is in scope
   rel : Pred (∀ i → Carrier (dom ⟨ i ⟩)) ρ -- some functions from `Fin nvar` to `dom`
   dec : Decidable rel

  -- scope size (i.e., # of vars involved in constraint)
  ∣s∣ : ℕ
  ∣s∣ = count T? s

  -- variables symbols (i.e., 0, 1, ..., nvar -1) zipped with true/false values from s
  i&s : Vec (Fin nvar × Bool) nvar
  i&s = zip (allFin nvar) s

  -- variables in scope along with T in second coordinate
  sfT : Vec (Fin nvar × Bool) _
  sfT = vec (filter (λ x → T? (snd x)) i&s)

  -- the scope function
  sf : Fin (vlength sfT) → Fin nvar
  sf i = fst (lookup sfT i)

  ScRestr : (∀ i → Carrier (dom ⟨ i ⟩)) → (∀ j → Carrier(dom ⟨ sf j ⟩))
  ScRestr f = f ∘ sf

  -- point-wise equality of functions
  _≐_ : Rel (∀ i → Carrier (dom ⟨ i ⟩)) ℓ
  f ≐ g = ∀ (i : Fin nvar) → (dom ⟨ i ⟩)._≈_ (f i) (g i)

  foldbool : (n : ℕ) (b : Bool) (f : Fin n → Bool) → Bool
  foldbool zero b f = b
  foldbool (suc n) b f = foldbool n (b ∧ (f (fromℕ n))) (λ i → f (raise 1 i))

  decide : (f g : (i : Fin nvar) → Carrier (dom ⟨ i ⟩)) → Bool
  decide f g = foldbool nvar true (λ i → does ((dom ⟨ i ⟩)._≟_ (f i) (g i)))

  ≐-dec : IsDecEquivalence _≐_

  IsDecEquivalence.isEquivalence ≐-dec = record { refl = λ i → (dom ⟨ i ⟩) .refl
                                                ; sym = λ x i → (dom ⟨ i ⟩) .sym (x i)
                                                ; trans = λ x y i → (dom ⟨ i ⟩) .trans (x i) (y i) }

  IsDecEquivalence._≟_ ≐-dec = λ x y → decide x y because {!!}

  -- point-wise equality of scope-restricted functions
  _≐s_ : Rel (∀ i → Carrier (dom ⟨ i ⟩)) ℓ
  f ≐s g = ∀ j → (dom ⟨ sf j ⟩)._≈_ (f (sf j)) (g (sf j))

 open Constraint

 _satisfies_ : (∀ i → Carrier (dom ⟨ i ⟩)) → Constraint → Type _
 f satisfies c = Σ[ g ∈ (∀ i → Carrier (dom ⟨ i ⟩)) ]
                 ( (g ∈ (rel c)) × ((_≐s_ c) f g))


 _satisfies?_ : (f : ∀ i → Carrier (dom ⟨ i ⟩)) → (c : Constraint) → Dec (f satisfies c)
 f satisfies? c = record { does = d ; proof = p }
  where
  d : Bool
  p : Reflects (f satisfies c) d
  d = {!!}
  p = {!!}


 record CSPInstance : Type (α ⊔ lsuc ρ)  where
  field
   ncon : ℕ      -- the number of constraints involved
   constr : Vec Constraint ncon

  -- f *solves* the instance if it satisfies all constraints.
  isSolution :  (∀ i → Carrier (dom ⟨ i ⟩)) → Type _
  isSolution f = All P constr
   where
   P : Pred Constraint _
   P c = f satisfies c


 record CSPInstanceList : Type (α ⊔ lsuc ρ)  where
  field
   constr : List Constraint

  -- f *solves* the instance if it satisfies all constraints.
  isSolution :  (∀ i → Carrier (dom ⟨ i ⟩)) → Bool
  isSolution f = all P constr
   where
   P : Constraint → Bool
   P c = does (f satisfies? c)


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

