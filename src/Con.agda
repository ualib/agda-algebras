--File: Congruence.agda
--Author: William DeMeo and Siva Somayyajula
--Date: 22 Feb 2020
--Updated: 23 Feb 2020
--Notes: Based on the parts of the file `basic.agda` (24 Dec 2019).

{-# OPTIONS --without-K --exact-split #-}

open import Preliminaries
open import Basic 
open import Hom

module Con {i j k : Level} {S : Signature i j}  where

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

con : (𝑨 : Algebra k S)
       -----------------------
  ->   Pred (Rel ∣ 𝑨 ∣ k) _
con 𝑨 = λ θ → IsEquivalence θ × compatible-alg 𝑨 θ
        --  -> 

--a single θ-class of A
_/_ : {A : Set k} -> (a : A) -> Rel A k -> Pred A _
a / θ = λ x → θ a x

--the collection of θ-classes of A
_//_ : (A : Set k) -> Rel A k -> Set _
A // θ = ∃ λ C -> (∃ λ a -> C ≡ a / θ)


_IsHomImageOf_ : (𝑩 : Algebra (lsuc k) S)
  ->             (𝑨 : Algebra k S)
  ->             Set _
𝑩 IsHomImageOf 𝑨 = ∃ λ (θ : Rel ∣ 𝑨 ∣ k) -> con 𝑨 θ -> (∣ 𝑨 ∣ // θ) ≃ ∣ 𝑩 ∣

-- HomImagesOf : Algebra k S -> Pred (Algebra (lsuc k) S) (i ⊔ j ⊔ lsuc k)
-- HomImagesOf 𝑨 = λ 𝑩 -> 𝑩 IsHomImageOf 𝑨 

HomImagesOf : Algebra k S -> Pred (Algebra _ S) _
HomImagesOf 𝑨 = λ 𝑩 -> 𝑩 IsHomImageOf 𝑨 

-- HomImagesOfClass : Pred (Algebra k S) (i ⊔ j ⊔ k) -> Pred (Algebra (lsuc k) S) _
-- HomImagesOfClass 𝓚 = λ 𝑩 -> ∃ λ 𝑨 -> 𝑨 ∈ 𝓚 × 𝑩 IsHomImageOf 𝑨

HomImagesOfClass : Pred (Algebra _ S) _ -> Pred (Algebra _ S) _
HomImagesOfClass 𝓚 = λ 𝑩 -> ∃ λ 𝑨 -> 𝑨 ∈ 𝓚 × 𝑩 IsHomImageOf 𝑨

IsHClosed : Pred (Pred (Algebra k S) _) _
IsHClosed = λ 𝓚 -> HomImagesOfClass 𝓚 ⊆ 𝓚
