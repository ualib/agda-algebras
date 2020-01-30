--File: subuniverse.agda
--Author: William DeMeo
--Date: 10 Jan 2020
--Updated: 11 Jan 2020


{-# OPTIONS --without-K --exact-split #-}

open import Level

open import basic
open algebra
open signature

module subuniverse {ℓ : Level} {S : signature} where

open import preliminaries

open import Data.Empty
open import Data.Unit.Base using (⊤)
open import Data.Product
open import Data.Sum using (_⊎_; [_,_])
open import Function
--open import Relation.Nullary hiding (Irrelevant)
open import Relation.Unary
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)



OpClosed : (A : algebra S) (B : Pred ⟦ A ⟧ᵤ ℓ) -> Set ℓ
OpClosed A B = ∀{𝓸 : ⟨ S ⟩ₒ}
               (args : Fin (⟨ S ⟩ₐ 𝓸) -> ⟦ A ⟧ᵤ) 
  ->           ∀(i : Fin (⟨ S ⟩ₐ 𝓸)) -> (args i) ∈ B
              -------------------------------------------
  ->           (A ⟦ 𝓸 ⟧) args ∈ B

record IsSubuniverse {A : algebra S} : Set (suc ℓ) where

  field
    sset : Pred ⟦ A ⟧ᵤ ℓ
    closed : OpClosed A sset    


--subalgebra type
record subalgebra (A : algebra S) : Set (suc ℓ) where

  field

    subuniv : Pred ⟦ A ⟧ᵤ ℓ
    _⟦_⟧ : (𝓸 : ⟨ S ⟩ₒ)
      ->   (args : Fin (⟨ S ⟩ₐ 𝓸) -> ⟦ A ⟧ᵤ)
      ->   ( ∀(i : Fin (⟨ S ⟩ₐ 𝓸)) -> (args i) ∈ subuniv )
         --------------------------------------------------
      ->   Set ℓ
      
    closed : OpClosed A subuniv



open IsSubuniverse

SubAlgebra : (A : algebra S)
  ->         (B : IsSubuniverse {A})
           --------------------------
  ->         (subalgebra A)

SubAlgebra A B =
  record
    {
    subuniv = sset B ;
    _⟦_⟧ = λ 𝓸 args p -> (sset B) ((A ⟦ 𝓸 ⟧) args) ;
    closed = closed B
    }



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
-- (2) is proved in the file quotient.agda
--
-- PROOF of (3).
--
-- (3) For every subset Y of A,
--     Sg(Y) = { t(a₁,...,aₙ) : t ∈ T(Xₙ), n < ω, and aᵢ ∈ Y, for i ≤ n}.
--
--  !!! TODO !!!
--
-- _⊆_ : ∀ {ℓ₃ ℓ ℓ₂} {Σ : signature} {A : Algebra {ℓ} {ℓ₂} Σ} →
--         Congruence {ℓ₃} A → Congruence {ℓ₃} A → Set _
-- Φ ⊆ Ψ = ∀ s → (rel Φ s) ⇒ (rel Ψ s)


