--File: free.agda
--Author: William DeMeo
--Date: 25 Dec 2019
--Updated: 10 Jan 2020
--Note: This was used for the second part of my talk at JMM Special Session.

{-# OPTIONS --without-K --exact-split #-}

open import Level
open import basic 
open signature

module free {S : signature}{X : Set} where

open import preliminaries  using (_⊎_ ; ∀-extensionality; ∑)
open import Function using (_∘_)
open import Relation.Unary
open import Relation.Binary hiding (Total)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; isEquivalence)
open Eq.≡-Reasoning
import Relation.Binary.EqReasoning as EqR

--------------------------------------------------------------

----------------------------
-- TERMS in the signature S
----------------------------

data Term : Set where
  generator : X -> Term
  node : ∀ (𝓸 : ⟨ S ⟩ₒ) -> (Fin (⟨ S ⟩ₐ 𝓸) -> Term) -> Term


----------------------------------
-- TERM ALGEBRA (for signature S)
----------------------------------

open algebra
open Term


free : algebra S

free = record { ⟦_⟧ᵤ = Term ; _⟦_⟧ = node }

--------------------------------------------------------------
-- analogue for setoid-based algebras

open Algebra

Free : Algebra S
Free = record {
         ⟦_⟧ᵣ = record {
                 Carrier = Term ;
                 _≈_ = _≡_ ;
                 isEquivalence = isEquivalence
                 } ;
         _⟦_⟧ = node  }

-------------------------------------
-- The UNIVERSAL PROPERTY of free
-- 1. every h : X -> ⟦ A ⟧ᵤ  lifts to a hom from free to A.
-- 2. the induced hom is unique.

-- PROOF.
-- 1.a. Every map  (X -> A)  "lifts".
free-lift : {A : algebra  S}(h : X -> ⟦ A ⟧ᵤ) -> ⟦ free ⟧ᵤ -> ⟦ A ⟧ᵤ
free-lift h (generator x) = h x
free-lift {A} h (node 𝓸 args) = (A ⟦ 𝓸 ⟧) λ{i -> free-lift {A} h (args i)}
-- 1.b. The lift is a hom.
open hom
lift-hom : {A : algebra S} (h : X -> ⟦ A ⟧ᵤ) -> hom free A
lift-hom {A} h = record { ⟦_⟧ₕ = free-lift {A} h; homo = λ args → refl }

-- 2. The lift to  (free -> A)  is unique.
--    (We need EXTENSIONALITY for this (imported from util.agda))
free-unique : {A : algebra S}
  ->    ( f g : hom free A )
  ->    ( ∀ x  ->  ⟦ f ⟧ₕ (generator x) ≡ ⟦ g ⟧ₕ (generator x) )
  ->    (t : Term)
       ---------------------------
  ->    ⟦ f ⟧ₕ t ≡ ⟦ g ⟧ₕ t

free-unique {A} f g p (generator x) = p x
free-unique {A} f g p (node 𝓸 args) =
   begin
     ⟦ f ⟧ₕ (node 𝓸 args)
   ≡⟨ homo f args  ⟩
     (A ⟦ 𝓸 ⟧) (λ i -> ⟦ f ⟧ₕ (args i))
   ≡⟨ cong ((A ⟦_⟧)_)
      ( ∀-extensionality λ i -> free-unique f g p (args i) ) ⟩
     (A ⟦ 𝓸 ⟧) (λ i -> ⟦ g ⟧ₕ (args i))
   ≡⟨ sym (homo g args) ⟩
     ⟦ g ⟧ₕ (node 𝓸 args)
   ∎

----------------------------------------
-- setoid-based analogues

open Setoid 
Free-Lift : {A : Algebra  S}(h : X -> Carrier ⟦ A ⟧ᵣ) -> Carrier ⟦ Free ⟧ᵣ -> Carrier ⟦ A ⟧ᵣ
Free-Lift h (generator x) = h x
Free-Lift {A} h (node 𝓸 args) = (A ⟦ 𝓸 ⟧) λ i -> Free-Lift {A} h (args i)

----------------------------------------

-- 1.b. The lift is a hom.

open Hom

Lift-Hom : {A : Algebra S} (h : X -> Carrier ⟦ A ⟧ᵣ) -> Hom Free A
Lift-Hom {A} h = record { ⟦_⟧ₕ = Free-Lift {A} h; Homo = λ args → Setoid.refl ⟦ A ⟧ᵣ }



--------------------------
--INTERPRETATION OF TERMS
--------------------------

--(cf Def 4.31 of Bergman)

--Let t ∈ Term be a term, A an algebra, in the signature S.
--We define an n-ary operation, denoted (t ̂ A), on A by recursion on
--the structure of t, as follows:

-- (1) if t is the variable x ∈ X and tup : X -> ⟦ A ⟧ᵤ is a tuple of elements of A,
--     then we define (t ̂ A) tup = tup x.

-- (2) if t = 𝓸 args, where 𝓸 ∈ ⟨ S ⟩ₒ is an operation symbol (of arity ⟨ S ⟩ₐ 𝓸),
--        args : ⟨ S ⟩ₐ 𝓸 -> Term is an (⟨ S ⟩ₐ 𝓸)-tuple of terms, and
--        tup : X -> ⟦ A ⟧ᵤ is a tuple of elements of A, then we define

--     (t ̂ A) tup = ((𝓸 args) ̂ A) tup
--                  = (A ⟦ 𝓸 ⟧) λ{ i -> ((args i) ̂ A) tup }


-- Here's the Agda implementation of the foregoing definition.

_̇_ : Term -> (A : algebra S) -> (X -> ⟦ A ⟧ᵤ) -> ⟦ A ⟧ᵤ
((generator x) ̇ A) tup = tup x
((node 𝓸 args) ̇ A) tup = (A ⟦ 𝓸 ⟧) λ{i -> (args i ̇ A) tup }

-- Recall, Theorem 4.32 of Bergman.
-- Let A and B be algebras of type S. Then the following hold:
--
--   (1) For every n-ary term t and homomorphism g: A —> B, 
--       g(tᴬ(a₁,...,aₙ)) = tᴮ(g(a₁),...,g(aₙ)).
--   (2) For every term t ∈ T(X) and every θ ∈ Con(A), 
--       a θ b => t(a) θ t(b).
--   (3) For every subset Y of A,
--       Sg(Y) = { t(a₁,...,aₙ) : t ∈ T(Xₙ), n < ω, and aᵢ ∈ Y, for i ≤ n}.
--
-- PROOF of (1)
--
-- (1) homomorphisms commute with terms
--
comm-hom-term : {A B : algebra S}
  ->    (g : hom A B) -> (t : Term)
  ->    (tup : X -> ⟦ A ⟧ᵤ)
       ------------------------------
  ->     ⟦ g ⟧ₕ ((t ̇ A) tup) ≡ (t ̇ B) (⟦ g ⟧ₕ ∘ tup)
--
comm-hom-term g (generator x) tup = Eq.refl
comm-hom-term {A} {B} g (node 𝓸 args) tup =  
-- Goal: ⟦ g ⟧ₕ ((A ⟦ 𝓸 ⟧) (λ { i → (args i ̇ A) tup })) ≡
--       (B ⟦ 𝓸 ⟧) (λ { i → (args i ̇ B) ((λ {.x} → ⟦ g ⟧ₕ) ∘ tup) })
  begin
    ⟦ g ⟧ₕ ((A ⟦ 𝓸 ⟧) (λ { i → (args i ̇ A) tup }))
  ≡⟨ homo g ( λ i → (args i ̇ A) tup )⟩
    (B ⟦ 𝓸 ⟧) ( λ i → ⟦ g ⟧ₕ ((args i ̇ A) tup) )
  ≡⟨ cong ((B ⟦_⟧)_)
     ( ∀-extensionality  λ i -> comm-hom-term g (args i) tup  ) ⟩
    (B ⟦ 𝓸 ⟧) ( λ i → (args i ̇ B) (⟦ g ⟧ₕ ∘ tup) )
  ∎

--
--
-- PROOF of (2).
--
-- (2) For every term t ∈ T(X) and every θ ∈ Con(A), 
--     a θ b => t(a) θ t(b).
--
open con

compatible-term : (A : algebra S)
 ->               (t : Term)
 ->               (θ : con A)
                 -------------------
 ->               compatible-fun (t ̇ A) ⟦ θ ⟧ᵣ

compatible-term A (generator x) θ p = p x
compatible-term A (node 𝓸 args) θ p =
  --Goal:
  -- ( ⟦ θ ⟧ᵣ Function.on
  --   ( λ tup -> (A ⟦ 𝓸 ⟧) (λ i -> (args i ̇ A) tup) )
  -- ) .i .j
  compat θ 𝓸 λ{ i -> (compatible-term A (args i) θ) p }

--------------------------------------------------------------
-- analogues for setoid-based algebras

open Setoid

_̂_ : Term -> (A : Algebra S) -> (X -> Carrier ⟦ A ⟧ᵣ) -> Carrier ⟦ A ⟧ᵣ
((generator x) ̂ A) tup = tup x
((node 𝓸 args) ̂ A) tup = (A ⟦ 𝓸 ⟧) λ{i -> (args i ̂ A) tup }

open Con

Compatible-Term :
    (A : Algebra S) -> (t : Term) -> (θ : Con A)
    ----------------------------------------------
  ->   compatible-fun (t ̂ A) ⟦ θ ⟧ᵣ

Compatible-Term A (generator x) θ p = p x
Compatible-Term A (node 𝓸 args) θ p =
  compat θ  λ{ k -> (Compatible-Term A (args k) θ) p }

--Function.on is the operation,
--  _on_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
--           → (B → B → C) → (A → B) → (A → A → C)
--  _*_ on f = λ x y → f x * f y
--
--So 
--  (⟦ θ ⟧ᵣ Function.on (λ tup → (A ⟦ 𝓸 ⟧) (λ { i → (args i ̂ A) tup }))) .i .j``
--means
--  ((λ tup → (A ⟦ 𝓸 ⟧) (λ { i → (args i ̂ A) tup })) .i)
--  ⟦ θ ⟧ᵣ
--  ((λ tup → (A ⟦ 𝓸 ⟧) (λ { i → (args i ̂ A) tup })) .j)
--Equivalently,
--   ⟦ θ ⟧ᵣ
--    (A ⟦ 𝓸 ⟧) (λ { i → (args i ̂ A) .i })
--    (A ⟦ 𝓸 ⟧) (λ { i → (args i ̂ A) .j })                   (1)
--We have,  ``p : lift-rel ⟦ θ ⟧ᵣ .i .j`` and the induction hypothesis,
--    ∀ i -> ⟦ θ ⟧ᵣ ((args i ̂ A) .i) ((args i ̂ A) .j)         (IH)
--which is equivalent to
--    lift-rel ⟦ θ ⟧ᵣ (λ { i → (args i ̂ A) .i }) (λ { i → (args i ̂ A) .j })
--Then we use
--    lift-rel ⟦ θ ⟧ᵣ =[ (A ⟦ 𝓸 ⟧) ]⇒ ⟦ θ ⟧ᵣ                    (2)
--to get (1).
--We get (2) from: compatible-alg A ⟦ θ ⟧ᵣ {𝓸}, which we get from ``compat θ {𝓸}``
--We get (IH) from: 
--
--  induct : (A : algebra S)
--    ->     (θ : con A)
--    ->     (args : Fin (⟨ S ⟩ₐ 𝓸) → Term)
--    ->     (i : Fin (⟨ S ⟩ₐ 𝓸))
--          -------------------
--    ->     compatible-fun (args i ̂ A) ⟦ θ ⟧ᵣ
--  induct A θ args i = compatible-term A (args i) θ 


-----------------------------


--After inserting `` (compat θ 𝓸) ?``, the  new goal is:
-- Goal: lift-rel ⟦ θ ⟧ᵣ (λ { i → (args i ̂ A) .i })
--       (λ { i → (args i ̂ A) .j })
-- ————————————————————————————————————————————————————————————
-- p    : lift-rel ⟦ θ ⟧ᵣ .i .j
-- .j   : X → ⟦ A ⟧ᵤ
-- .i   : X → ⟦ A ⟧ᵤ
-- θ    : con A
-- args : Fin (⟨ S ⟩ₐ 𝓸) → Term
-- 𝓸    : ⟨ S ⟩ₒ
-- A    : algebra S
-- X    : Set
-- S    : signature

--------------------------------------------------
