--File: birkhoff.agda
--AUTHOR: William DeMeo
--DATE: 13 Jan 2020
--UPDATED: 24 Jan 2020

open import Level
open import basic
open import subuniverse
open algebra
open signature
open import preliminaries
open import Relation.Unary
open import Relation.Binary.Core
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)

module birkhoff {S : signature} where

ker : {A : Set} {B : Set} (f : A -> B) -> A -> A -> Prp
ker f  = λ x y -> f x ≡ f y

-- Ker : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂} (f : A -> B) -> A -> A -> Prp {ℓ₂}
-- Ker f  = λ x y -> f x ≡ f y

-------------
-- FUNCTIONS
-------------

--equalizer
E : {A : Set} {B : Set}
    (f g : A -> B) -> A -> Prp
E = λ f g x -> f x ≡ g x

--equalizer of homs
open hom
E-hom : {A B : algebra S}
        (f g : hom A B) -> (⟦ A ⟧ᵤ) -> Prp
E-hom f g a = ⟦ f ⟧ₕ a ≡ ⟦ g ⟧ₕ a

--surjectivity
epic : {A B : Set} (g : A -> B) -> Prp
epic g = ∀ y -> Image g ∋ y

--injectivity
monic : {A B : Set} (g : A -> B) -> Prp
monic g = ∀ x₁ x₂ -> g x₁ ≡ g x₂ -> x₁ ≡ x₂

--bijectivity
bijective : {A B : Set} (g : A -> B) -> Prp
bijective g = epic g ∧ monic g

---------------------------------------------------------------------

--------------
-- VARIETIES
--------------

--cf Def 1.10 of Bergman
--Let 𝓚 be a class of similar algebras. We write
--  H(𝓚) for the class of all homomorphic images of members of 𝓚;
--  S(𝓚) for the class of all algebras isomorphic to a subalgebra of a member of 𝓚;
--  P(𝓚) for the class of all algebras isomorphic to a direct product of members of 𝓚;
--We say that 𝓚 is closed under the formation of homomorphic images if H(𝓚) ⊆ 𝓚,
--and similarly for subalgebras and products.
--Notice that all three of these "class operators" are designed so that for any
--class 𝓚, H(𝓚), S(𝓚), P(𝓚) are closed under isomorphic images.
--On those rare occasions that we need it, we can write I(𝓚) for the class of algebras
--isomorphic to a member of 𝓚.
--Finally, we call 𝓚 a VARIETY if it is closed under each of H, S and P.

contains : {A : Set} -> (L : List A) -> A -> Prp
contains [] a = ⊥
contains (h :: tail) a = (h ≡ a) ∨ (contains tail a)

--data class-of-algebras : Set where

-- --Hom-closed
-- H-closed : (𝓚 : Pred (algebra S)) -> Prp
-- H-closed 𝓚 = ∀ (A : algebra S)  ->  (𝓚 A)
--   ->     (∃ θ : Con A)   ->   (∃ C : algebra S)
--   ->     (𝓚 C) ∧ (A / θ ≅ C)

-- --Sub-closed
-- -- SC : (𝓚 : List (algebra S)) -> Prp
-- -- SC 𝓚 = ∀(A : algebra S) -> (contains 𝓚 A)
-- --   -> (B : subalgebra A) -> (∃ C : algebra S)
-- --   -> (contains 𝓚 C) ∧ B ≃ C
