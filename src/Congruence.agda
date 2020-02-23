--File: Congruence.agda
--Author: William DeMeo and Siva Somayyajula
--Date: 22 Feb 2020
--Updated: 22 Feb 2020
--Notes: Based on the parts of the file `basic.agda` (24 Dec 2019).

{-# OPTIONS --without-K --exact-split #-}

open import Preliminaries
open import Basic 
open import Hom

module Congruence {i j k : Level} {S : Signature i j}  where

-- lift a binary relation from pairs to pairs of tuples.
lift-rel : ∀{ℓ₁ : Level} {Idx : Set ℓ₁} {ℓ₂ : Level} {Z : Set ℓ₂}
  ->         Rel Z ℓ₂
          -----------------
  ->       Rel (Idx -> Z) (ℓ₁ ⊔ ℓ₂)
lift-rel R = λ args₁ args₂ -> ∀ i -> R (args₁ i) (args₂ i)

-- compatibility of a give function-relation pair
compatible-fun : ∀ {ℓ₁ ℓ₂ : Level} {γ : Set ℓ₁} {Z : Set ℓ₂}
  ->             ((γ -> Z) -> Z)
  ->             (Rel Z ℓ₂)
                -----------------------------------------
  ->             Set (ℓ₁ ⊔ ℓ₂)
compatible-fun f 𝓻 = (lift-rel 𝓻) =[ f ]⇒ 𝓻

-- relation compatible with an operation
compatible : (𝑨 : Algebra k S)
  ->         ∣ S ∣
  ->         Rel ∣ 𝑨 ∣ k
           -------------------------------
  ->         Set (j ⊔ k)
compatible 𝑨 𝓸 𝓻 =
  (lift-rel {j} {⟦ S ⟧ 𝓸} {k} {∣ 𝑨 ∣}  𝓻) =[ (⟦ 𝑨 ⟧ 𝓸) ]⇒ 𝓻

-- relation compatible with all operations of an algebra
compatible-alg : (𝑨 : Algebra k S)
  ->            Rel ∣ 𝑨 ∣ k
              ------------------------------
  ->             Set (i ⊔ j ⊔ k)
compatible-alg 𝑨 𝓻 = ∀ 𝓸 -> compatible 𝑨 𝓸 𝓻

-- Congruence relations
Con : (𝑨 : Algebra k S)
       -----------------------
  ->    Set (i ⊔ j ⊔ lsuc k)
--  ->    Set (lsuc i ⊔ lsuc j ⊔ lsuc k)
Con 𝑨 = ∃ λ (θ : Rel ∣ 𝑨 ∣ k)
          -> IsEquivalence θ × compatible-alg 𝑨 θ

