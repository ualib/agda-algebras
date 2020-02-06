--File: quotient.agda
--AUTHOR: William DeMeo
--DATE: 28 Jan 2020
--UPDATED: 28 Jan 2020

open import Level
open import basic
open import subuniverse
open signature
open import preliminaries

module quotient {ℓ : Level} {S : signature} where


--open import Function
open import Relation.Unary
open import Relation.Binary
open import Relation.Binary.Core
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)


---------------------------
-- CONGRUENCE RELATIONS
--------------------------

-- Reflexive : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
-- Reflexive _∼_ = ∀ {x} → x ∼ x

open algebra

isCompatible : ∀ (A : algebra S) -> Rel ⟦ A ⟧ᵤ zero -> Set _

isCompatible A θ = ∀{𝓸 : ⟨ S ⟩ₒ}
  ->               (arg1 arg2 : Fin (⟨ S ⟩ₐ 𝓸) -> ⟦ A ⟧ᵤ) 
  ->               ( ∀ i -> θ (arg1 i) (arg2 i) )
                 -------------------------------------------
  ->                 θ ((A ⟦ 𝓸 ⟧) arg1) ((A ⟦ 𝓸 ⟧) arg2)



open Setoid
open Algebra


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
-- (1) is proved in the file free.agda
--
-- PROOF of (2).

-- (2) For every term t ∈ T(X) and every θ ∈ Con(A), 
--     a θ b => t(a) θ t(b).
--


-- TODO



--------------------------------------------------------------
--EARLIER/OTHER ATTEMPTS
-------------------------------------------------------------

-----------------
-- congruences
-----------------
-- record congruence (A : algebra S) : Set₁ where
--   field
--     ⟦_⟧ᵣ : Rel {zero} ⟦ A ⟧ᵤ zero
--     eqv : IsEquivalence ⟦_⟧ᵣ
--     compatible : (𝓸 : ⟨ S ⟩ₒ) -> (args₁ args₂ : Fin (⟨ S ⟩ₐ 𝓸) -> ⟦ A ⟧ᵤ)
--       ->         ∀ (i : Fin (⟨ S ⟩ₐ 𝓸)) -> ⟦_⟧ᵣ (args₁ i) (args₂ i)
--                 ---------------------------------------------------
--       ->           ⟦_⟧ᵣ ((A ⟦ 𝓸 ⟧) args₁) ((A ⟦ 𝓸 ⟧) args₂)
      
-- open congruence

-- postulate  -- (for now... prove this later)
--   cong-term : (A : algebra  S)
--     ->        (θ : congruence A)
--     ->        (t : Term)
--     ->        (tup₁ tup₂ : X -> ⟦ A ⟧ᵤ)
--     ->        ( ∀(x : X) -> ⟦ θ ⟧ᵣ (tup₁ x) (tup₂ x) )
--             ---------------------------------------------
--     ->         ⟦ θ ⟧ᵣ ((t ̂ A) tup₁) ((t ̂ A) tup₂)

-- cong-term A θ (generator x) tup₁ tup₂ p = p x
-- cong-term A θ (node 𝓸 args) tup₁ tup₂ p =  
--   compatible θ 𝓸 (λ{ i -> (args i ̂ A) tup₁ }) (λ{ i -> (args i ̂ A) tup₂ }) 
--     ∀ i : ⟨ S ⟩ₐ 𝓸) -> ? --(cong-term A θ (args i) tup₁ tup₂ p) )

-- HOW TO PROVE THIS --
-- Goal is:
-- ⟦ θ ⟧ᵣ ((A ⟦ 𝓸 ⟧) (λ { i → (args i ̂ A) tup₁ }))
--       ((A ⟦ 𝓸 ⟧) (λ { i → (args i ̂ A) tup₂ }))

-- So let args₁ = (λ { i → (args i ̂ A) tup₁ })
-- and    args₂ = (λ { i → (args i ̂ A) tup₁ })
-- WTS
--    ⟦ θ ⟧ᵣ ((A ⟦ 𝓸 ⟧) args₁) ((A ⟦ 𝓸 ⟧) args₂)

-- ...which follows from:

-- (compatible θ) 𝓸 (λ { i → (args i ̂ A) tup₁ })) (λ { i → (args i ̂ A) tup₂ })) p'

-- where p' :  ∀ (i : ⟨ S ⟩ₐ 𝓸) -> ⟦ θ ⟧ᵣ (args₁ i) (args₂ i))

-- but (args₁ i)  = (args i ̂ A) tup₁ and (args₂ i)  = (args i ̂ A) tup₂.

-- so   p' :   ∀ (i : ⟨ S ⟩ₐ 𝓸) -> ⟦ θ ⟧ᵣ ((args i ̂ A) tup₁) ((args i ̂ A) tup₂)

-- By induction, for each i,

-- ⟦ θ ⟧ᵣ ((args i ̂ A) tup₁) ((args i ̂ A) tup₂) holds by

--  (cong-term θ (args i) tup₁ tup₂ ?) )

-- (Recall, the original p is a proof of (x : X) → ⟦ θ ⟧ᵣ (tup₁ x) (tup₂ x))


