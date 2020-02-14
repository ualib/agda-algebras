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

data monoid-op : Set where
  e : monoid-op
  · : monoid-op
  
monoid-sig : signature 
monoid-sig =
  record
    { _Ω = ℕ
    ; _𝓕 = monoid-op
    ; _ρ = λ {e -> 0; · -> 2}
    }


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
 
--Here are 3 flavors of algebras.

--1. algebra (with carrier of type Set)
record algebra (S : signature) : Set₁ where

  field 
    ⟦_⟧ᵤ : Set
    _⟦_⟧ : (𝓸 : S 𝓕) -> (ℕ -> ⟦_⟧ᵤ) -> ⟦_⟧ᵤ

-- 2. algebra (with carrier a predicate on Ω)
record algebraP (S : signature) : Set₁ where

  field
    ⟦_⟧ₚ : Pred (S Ω) zero
    _⟦_⟧ₒ : (𝓸 : S 𝓕) -> (ℕ -> (S Ω)) -> (S Ω) -- I don't like this type signature.
    cl : ∀ (𝓸 : S 𝓕) (args : ℕ -> (S Ω))      --  (it's very imprecise)   :'(
         -> (∀(i : ℕ) -> (args i) ∈ ⟦_⟧ₚ)
        ------------------------------------------------
         -> _⟦_⟧ₒ 𝓸 args ∈ ⟦_⟧ₚ

open B.Setoid

-- 3. algebra (with carrier a Setoid)
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
  constructor mkhom
  field

    -- The map:
    ⟦_⟧ₕ : ⟦ A ⟧ᵤ -> ⟦ B ⟧ᵤ 

    -- The property the map must have to be a hom:
    homo : ∀ {𝓸 : S 𝓕} (args : ℕ -> ⟦ A ⟧ᵤ)
           ->  ⟦_⟧ₕ ((A ⟦ 𝓸 ⟧) args) ≡ (B ⟦ 𝓸 ⟧) (⟦_⟧ₕ ∘ args)

--------------------------------------------------------------
-- analogue for predicate-based algebras

open algebraP

record homP {S : signature}
  (A : algebraP S) (B : algebraP S) : Set where

  field

    -- The map:
    hmap : S Ω -> S Ω  -- <-- type is not very precise :'(

    -- The property the map must have to be a hom:
    homoP : ∀ {𝓸 : S 𝓕} (args : ℕ -> (S Ω))
           ->  hmap ((A ⟦ 𝓸 ⟧ₒ) args) ≡ (B ⟦ 𝓸 ⟧ₒ) (hmap ∘ args)

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
  ->    ( (⟦ g ⟧ₕ ∘ ⟦ f ⟧ₕ) ≡ identity _ ) -- ⟦ A ⟧ᵤ
      ∧ ( (⟦ f ⟧ₕ ∘ ⟦ g ⟧ₕ) ≡ identity _ ) -- ⟦ B ⟧ᵤ 

--------------------------------------------------------------
-- analogue for predicate-based algebras

open homP

_≅ₚ_ :  {S : signature}
       (A : algebraP S) -> (B : algebraP S) -> Set _

A ≅ₚ B = (∃ f : homP A B)
  ->    (∃ g : homP B A)
  ->    ( (hmap g) ∘ (hmap f) ≡ identity _ )
      ∧ ( (hmap f) ∘ (hmap g) ≡ identity _ )

--------------------------------------------------------------
-- analogue for setoid-based algebras

open Hom

_≅ₛ_ : {S : signature}
      (A : Algebra S) -> (B : Algebra S) -> Set _

A ≅ₛ B = (∃ f : Hom A B)
  ->    (∃ g : Hom B A)
  ->    ( (⟦ g ⟧ₕ ∘ ⟦ f ⟧ₕ) ≡ identity _ ) -- (Carrier ⟦ A ⟧ᵣ) )
      ∧ ( (⟦ f ⟧ₕ ∘ ⟦ g ⟧ₕ) ≡ identity _ ) -- (Carrier ⟦ B ⟧ᵣ)  )


lift-rel : {ℓ : Level} {Idx : Set} {X : Set}
  ->         Rel X ℓ
          -----------------
  ->       Rel (Idx -> X) ℓ
lift-rel R = λ args₁ args₂ -> ∀ i -> R (args₁ i) (args₂ i)

compatible-fun : ∀{α γ : Set}
  ->   ((γ -> α) -> α)  ->  (Rel α zero)  ->  Set
compatible-fun f 𝓻 = (lift-rel 𝓻) =[ f ]⇒ 𝓻

-- relation compatible with an operation
compatible : ∀ {S : signature}
  ->  (A : algebra S)  ->   S 𝓕  
  ->   Rel ⟦ A ⟧ᵤ zero  ->  Set _
compatible A 𝓸 𝓻 = (lift-rel 𝓻) =[ (A ⟦ 𝓸 ⟧) ]⇒ 𝓻

-- relation compatible with all operations of an algebra
compatible-alg : ∀ {S : signature}
  ->  (A : algebra S) -> Rel ⟦ A ⟧ᵤ zero -> Set _
compatible-alg {S} A 𝓻 = ∀ 𝓸 -> compatible A 𝓸 𝓻


record con {S : signature} (A : algebra S) : Set₁ where
  field
    ⟦_⟧ᵣ : Rel ⟦ A ⟧ᵤ zero
    equiv : IsEquivalence ⟦_⟧ᵣ
    compat : compatible-alg A ⟦_⟧ᵣ

-----------------------------------------------------------
-- Analogues for predicate-based algebras.
compatibleP : ∀ {S : signature}
  ->  (A : algebraP S)  ->   S 𝓕  
  ->   Rel (S Ω) zero  ->  Set _
compatibleP A 𝓸 𝓻 = (lift-rel 𝓻) =[ (A ⟦ 𝓸 ⟧ₒ) ]⇒ 𝓻

compatible-algP : ∀ {S : signature}
  ->  (A : algebraP S) -> Rel (S Ω) zero -> Set _
compatible-algP {S} A 𝓻 = ∀ 𝓸 -> compatibleP A 𝓸 𝓻

record conP {S : signature} (A : algebraP S) : Set₁ where
  field
    𝓡 : Rel (S Ω) zero     -- type 𝓡 as `\MCR`
    equivP : IsEquivalence 𝓡
    compatP : compatible-algP A 𝓡

----------------------------------------------------------
-- Analogues for setoid-based algebras

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



------------------------------------------------------------------
-------------    MISC EXPERIMENTAL STUFF (not used)  -------------

-- compatible-fun : ∀{S : signature}{X : Set} --{n : ℕ}
--   -> (A : algebra S) -> ((X -> ⟦ A ⟧ᵤ) -> ⟦ A ⟧ᵤ)  
--   ->  (Rel ⟦ A ⟧ᵤ zero)  ->  Set
-- compatible-fun A f 𝓻 = compatible-func f 𝓻

-----------------------------
--Nullary symbols (contants)
-----------------------------
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

-- Induction. For a proof by structural induction over a recursively defined
-- data type, make a hole, enter the hole, and type C-c C-c; when prompted,
-- enter the symbol over which you wish to induct.



