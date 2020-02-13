--File: basic.agda
--Author: William DeMeo
--Date: 24 Dec 2019
--Updated: 10 Jan 2020
--Note: This was used for the first part of my talk at JMM Special Session.

{-# OPTIONS --without-K --exact-split #-}

--without-K disables Streicher's K axiom (see "NOTES on Axiom K" below).

--exact-split makes Agda to only accept definitions with the equality sign "=" that
--behave like so-called judgmental or definitional equalities.


module basic where

open import Level
open import preliminaries
open import Relation.Unary
import Relation.Binary as B
--import Relation.Binary.Indexed as I
open import Relation.Binary.Core
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Function using (_∘_)
open import Function.Equality hiding (_∘_)


open import Agda.Builtin.Nat public
  renaming ( Nat to ℕ; _-_ to _∸_; zero to nzero; suc to succ )
--  using    ( _+_; _*_ )

-- open import Data.Fin public
--   -- (See "NOTE on Fin" section below)
--   hiding ( _+_; _<_ )
--   renaming ( suc to fsucc; zero to fzero )

-----------------------------------------------


--------------------------------
-- A data type for SIGNATURES
--------------------------------

record signature : Set₁ where 
  field
    _Ω : Set         -- The "überuniverse" (all universes are subsets of Ω)
    _𝓕 : Set        -- operation symbols.
    _ρ : _𝓕 -> ℕ   -- Each operation symbol has an arity.
                      
-- (for now, use natural number arities, but this isn't essential)

--   If   σ : signature   is a signature...
--     σ Ω denotes the überuniverse of S.
--     σ 𝓕 denotes the operation symbols of S.
--   If  𝓸 : σ 𝓕  is an operation symbol...
--       (σ ρ 𝓸) is the arity of 𝓸.


-----------------------------------------------


-----------------------------
--A data type for OPERATIONS
-----------------------------


data operation (γ α : Set) : Set where

  o : ((γ -> α) -> α) -> operation γ α

-- Here, γ is an "arity type" and α is a "universe type".

-- Example: the i-th γ-ary projection operation on α

-- could be implemented like this:

π : ∀ {γ α : Set} -> (i : γ) -> operation γ α

π i =  o λ x -> x i


-----------------------------------

-----------------------------
--A data type for ALGEBRAS
-----------------------------

open signature
 
-- basic algebra
record algebra (S : signature) : Set₁ where

  field 
    ⟦_⟧ᵤ : Set
    _⟦_⟧ : (𝓸 : S 𝓕) -> (ℕ -> ⟦_⟧ᵤ) -> ⟦_⟧ᵤ

-- basic algebra
record algebraP (S : signature) : Set₁ where

  field
    ⟦_⟧ₚ : Pred (S Ω) zero
    _⟦_⟧ₒ : (𝓸 : S 𝓕) -> (ℕ -> (S Ω)) -> (S Ω)
    cl : ∀ (𝓸 : S 𝓕) (args : ℕ -> (S Ω))
         -> (∀(i : ℕ) -> (args i) ∈ ⟦_⟧ₚ)
        ------------------------------------------------
         -> _⟦_⟧ₒ 𝓸 args ∈ ⟦_⟧ₚ


--basic algebra on a given universe
record algebra_on (S : signature) (X : Set) (B : Pred X zero) : Set  where
  field
     --    car : (x : X) -> B x
    _⟦_⟧s : (𝓸 : S 𝓕) -> (ℕ -> (x : X) -> B x) -> ((x : X) -> B x)

-- mkalgebra : (S : signature) -> (X : Set) -> (B : Pred X zero)
--   -> (A : algebra_on S X B) -> algebra S
-- mkalgebra S X B A = record { ⟦_⟧ᵤ = X; _⟦_⟧ = _⟦_⟧s A }

open B.Setoid

-- setoid-based algebra (algebra whose carrier is a setoid)
record Algebra (S : signature) : Set₁ where

  field
    ⟦_⟧ᵣ : B.Setoid zero zero
    _⟦_⟧ : (𝓸 : S 𝓕) -> (ℕ -> Carrier ⟦_⟧ᵣ) ->  Carrier ⟦_⟧ᵣ


----------------------------------
--A data type for HOMOMORPHISMS
----------------------------------

open algebra

record hom {S : signature}
  (A : algebra S) (B : algebra S) : Set where

  field

    -- The map:
    ⟦_⟧ₕ : ⟦ A ⟧ᵤ -> ⟦ B ⟧ᵤ 

    -- The property the map must have to be a hom:
    homo : ∀ {𝓸 : S 𝓕} (args : ℕ -> ⟦ A ⟧ᵤ)
           ->  ⟦_⟧ₕ ((A ⟦ 𝓸 ⟧) args) ≡ (B ⟦ 𝓸 ⟧) (⟦_⟧ₕ ∘ args)

--------------------------------------------------------------
-- analogue for setoid-based algebras

open Algebra

record Hom {S : signature}
  (A : Algebra S) (B : Algebra S) : Set where

  field

    -- The map:
    ⟦_⟧ₕ : Carrier ⟦ A ⟧ᵣ -> Carrier ⟦ B ⟧ᵣ 

    -- The property the map must have to be a hom:
    Homo : ∀ {𝓸 : S 𝓕} (args : ℕ -> Carrier ⟦ A ⟧ᵣ)
      ->   (_≈_ ⟦ B ⟧ᵣ)  ⟦ (A ⟦ 𝓸 ⟧) args ⟧ₕ  ( (B ⟦ 𝓸 ⟧) (⟦_⟧ₕ ∘ args) )


---------------------
--ISOMORPHISM
---------------------

open hom

_≅ᵤ_ :  {S : signature}
       (A : algebra S) -> (B : algebra S) -> Set _

A ≅ᵤ B = (∃ f : hom A B)
  ->    (∃ g : hom B A)
  ->    ( (⟦ g ⟧ₕ ∘ ⟦ f ⟧ₕ) ≡ identity ⟦ A ⟧ᵤ )
      ∧ ( (⟦ f ⟧ₕ ∘ ⟦ g ⟧ₕ) ≡ identity ⟦ B ⟧ᵤ )

--------------------------------------------------------------
-- analogue for setoid-based algebras

open Hom

_≅_ : {S : signature}
      (A : Algebra S) -> (B : Algebra S) -> Set _

A ≅ B = (∃ f : Hom A B)
  ->    (∃ g : Hom B A)
  ->    ( (⟦ g ⟧ₕ ∘ ⟦ f ⟧ₕ) ≡ identity (Carrier ⟦ A ⟧ᵣ) )
      ∧ ( (⟦ f ⟧ₕ ∘ ⟦ g ⟧ₕ) ≡ identity (Carrier ⟦ B ⟧ᵣ)  )


lift-rel : {ℓ : Level} {Idx : Set} {X : Set}
  ->         Rel X ℓ
          -----------------
  ->       Rel (Idx -> X) ℓ
lift-rel R = λ args₁ args₂ -> ∀ i -> R (args₁ i) (args₂ i)


compatible-fun : ∀{α γ : Set}
  ->   ((γ -> α) -> α)  ->  (Rel α zero)  ->  Set
compatible-fun f 𝓻 = (lift-rel 𝓻) =[ f ]⇒ 𝓻

-- compatible-fun : ∀{S : signature}{X : Set} --{n : ℕ}
--   -> (A : algebra S) -> ((X -> ⟦ A ⟧ᵤ) -> ⟦ A ⟧ᵤ)  
--   ->  (Rel ⟦ A ⟧ᵤ zero)  ->  Set
-- compatible-fun A f 𝓻 = compatible-func f 𝓻

compatible : ∀ {S : signature}
  ->  (A : algebra S)  ->   S 𝓕  
  ->   Rel ⟦ A ⟧ᵤ zero  ->  Set _
compatible A 𝓸 𝓻 = (lift-rel 𝓻) =[ (A ⟦ 𝓸 ⟧) ]⇒ 𝓻

compatible-alg : ∀ {S : signature}
  ->  (A : algebra S) -> Rel ⟦ A ⟧ᵤ zero -> Set _
compatible-alg {S} A 𝓻 = ∀ 𝓸 -> compatible A 𝓸 𝓻


record con {S : signature} (A : algebra S) : Set₁ where
  field
    ⟦_⟧ᵣ : Rel ⟦ A ⟧ᵤ zero
    equiv : IsEquivalence ⟦_⟧ᵣ
    compat : compatible-alg A ⟦_⟧ᵣ

---------------------------------------------
-- analogues for setoid-based algebras

Compatible : ∀ {S : signature}
  ->            S 𝓕  ->  (A : Algebra S)
  ->            Rel (Carrier ⟦ A ⟧ᵣ) zero -> Set _
Compatible 𝓸 A 𝓻 = (lift-rel 𝓻) =[ (A ⟦ 𝓸 ⟧) ]⇒ 𝓻

Compatible-Alg : ∀ {S : signature}
  -> (A : Algebra S) -> Rel (Carrier ⟦ A ⟧ᵣ) zero -> Set _
Compatible-Alg {S} A 𝓻 = ∀{𝓸 : S 𝓕} -> Compatible 𝓸 A 𝓻


record Con {S : signature} (A : Algebra S) : Set₁ where
  field
    ⟦_⟧ᵣ : Rel (Carrier ⟦ A ⟧ᵣ) zero
    equiv : IsEquivalence ⟦_⟧ᵣ
    compat : Compatible-Alg A ⟦_⟧ᵣ

open Con


Quotient : {S : signature} (A : Algebra S) -> (θ : Con A) -> Algebra S

Quotient A θ =
  record {

    ⟦_⟧ᵣ = record {
            Carrier = Carrier ⟦ A ⟧ᵣ ;
            _≈_ = ⟦ θ ⟧ᵣ;
            isEquivalence = equiv θ } ;

    _⟦_⟧ = A ⟦_⟧ }


-- -----------------------------
-- --Nullary symbols (contants)
-- -----------------------------

-- open signature

-- const : ∀ {S : signature} -> (𝓸 : ⟨ S ⟩ₒ) -> Set _
-- const {S} 𝓸 = ⟨ S ⟩ₐ 𝓸 ≡ nzero

-- constants : (S : signature) -> Pred ⟨ S ⟩ₒ _
-- constants S 𝓸 = (const {S} 𝓸)



-- OLD VERSION
-- IsCompatible : {S : signature}
--                (A : Algebra S) -> Rel (Carrier ⟦ A ⟧ᵣ) zero -> Set _

-- IsCompatible {S} A θ = ∀{𝓸 : ⟨ S ⟩ₒ}
--   ->               (arg1 arg2 : Fin (⟨ S ⟩ₐ 𝓸) -> Carrier ⟦ A ⟧ᵣ) 
--   ->               ( ∀ i -> θ (arg1 i) (arg2 i) )
--                  -------------------------------------------
--   ->               θ ((A ⟦ 𝓸 ⟧) arg1) ((A ⟦ 𝓸 ⟧) arg2)

-----------------------------------------------

----------------
--NOTES on Fin
----------------
-- Previously, we used our own Fin type, defined as follows
--
-- data Fin : Nat -> Set where
--   fzero : {n : Nat} -> Fin (succ n)
--   fsucc : {n : Nat} -> Fin n -> Fin (succ n)
--
--fzero belongs to Fin (succ n) for every n, and if a belongs
--to Fin n, then fsucc a belongs to Fin (succ n).
--
-- data Empty : Set where
--   empty : Fin zero -> Empty
--
--Example. turn a list into a function from indices to elements.
--
-- _!_ : {n : Nat}{A : Set} -> Vec A n -> Fin n -> A
-- [] ! ()
-- (x :: xs) ! fzero = x
-- (x :: xs) ! (fsucc i) = xs ! i
--
--inversely, turn a function (from indices to elements) into a
--list of values of the function.
--
-- tabulate : {n : nat}{a : set} -> (fin n -> a) -> vec a n
-- tabulate {zero} f = []
-- tabulate {succ n} f = f fzero :: tabulate (f ∘ fsucc)
--
--note that tabulate is defined by recursion over the length of the
--result list, even though it is an implicit argument.
--

------------------------------------------------------------

---------------
--NOTES on ≡
---------------
--(see: p.12 of norell-chapman, p.23 of bove-dybjer) 
--
-- data _≡_ {a : set} (x : a) : a → set where
--   refl : x ≡ x
--
-- data _==_ {a : set} : a -> a -> set where
--   refl : (a : a) -> a == a
--
-- {-# builtin equality _≡_ #-}
--
--The rule of ==-elimination is the rule that allows
--us to substitute equals for equals:
--(see p.23 of Bove-Dybjer) 
--
-- subst : {A : Set} -> {C : A -> Set} -> {x y : A} -> x == y -> C x -> C y
-- subst (refl a) c = c
--
--This is proved by pattern matching: the only possibility
--to prove a == b is if they have the same canonical form c.
--In this case, (the canonical forms of) C a and C b
--are also the same; hence they contain the same elements.
--
--The K and S combinators
--(see: Bove-Dybjer, p. 8)
--
-- K : (A B : Set) -> A -> B -> A
-- K _ _ x _ = x
--
-- S : (A B C : Set) -> (A -> B -> C) -> (A -> B) -> A -> C
-- S _ _ _ f g x = f x (g x)
--
--(see: Bove-Dybjer, p. 9)
--
-- if_then_else_ : {C : Set} -> Bool -> C -> C -> C
-- if true then x else y = x
-- if false then x else y = y
--
--(Note the mix-fix syntax and the implicit argument which gives a readable version.)
--
--The primitive recursion combinator for natural numbers.
--(see: Bove-Dybjer, p. 9)
--
-- natrec : {C : Set} -> C -> (Nat -> C -> C) -> Nat -> C
-- natrec p h zero = p
-- natrec p h (succ n) = h n (natrec p h n)
--
-- From Bove-Dybjer, p. 9.
--
--   "It is a functional (higher-order function) defined by primitive 
--   recursion. It receives four arguments: the first (which is implicit)
--   is the return type, the second (called p in the equations) is the
--   element returned in the base case, the third (called h in the 
--   equations) is the step function, and the last is the natural 
--   number on which we perform the recursion"
--
--Here is how we could define add and mult on nat using natrec.
--(see: Bove-Dybjer, p. 10)
--
-- plus : Nat -> Nat -> Nat
-- plus n m = natrec m (\x y -> succ y) n
--
-- mult : Nat -> Nat -> Nat
-- mult n m = natrec zero (\x y -> plus y m) n
--
--Example proof.
--Suppose we wish to prove that the two addition functions we have
--defined, + and plus, given the same result.  Here's how:
--
-- eq-plus-rec : (n m : Nat) -> ((n + m) == plus n m)
-- eq-plus-rec n m = natrec (refl m) (\k' ih -> eq-succ ih) n




--------------------------------------------------------------------------------

-- Here is the Agda key-binding technique that was briefly mentioned.

---------------------------------------
-- Writing definitions interactively
--------------------------------------

-- Add a question mark and then type C-c C-l to create a new "hole."

-- Type C-c C-f to move into the next unfilled hole.

-- Type C-c C-c (from inside the hole) to be prompted for what type should
-- fill the given hole.

-- Type m to split on the variable in the hole.

-- Type C-c C-f to move into the next hole.

-- Type C-c C-, to get the type required in the current hole.

-- Enter an appropriate object in the hole and type C-c C-space to remove the hole.

{- SUMMARY
   ? then C-c C-l creates hole
   C-c C-f moves to next hole
   C-c C-c prompts for what goes in hole
   m splits on variable in hole
   C-c C-, in hole gets type required
   C-c C-space removes hole
-}

-------------
-- INDUCTion.
--------------

-- For a proof by structural induction over a recursively defined data type, make a hole,
-- enter the hole, and type C-c C-c; when prompted, enter the symbol over which
-- you wish to induct.


--------------------------------------------

