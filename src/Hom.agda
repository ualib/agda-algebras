--File: Hom.agda
--Author: William DeMeo and Siva Somayyajula
--Date: 20 Feb 2020
--Updated: 23 Feb 2020

{-# OPTIONS --without-K --exact-split #-}

open import Preliminaries
open import Basic

module Hom {i j k l m : Level} {S : Signature i j} {𝑨 : Algebra k S} {𝑩 : Algebra l S} {𝑪 : Algebra m S} where


-- private
--   variable
--     i j k l m : Level
--     S : Signature i j
--     𝑨 : Algebra k S
--     𝑩 : Algebra l S
--     𝑪 : Algebra m S


--The category of algebras Alg with morphisms as Homs
Hom : {ℓ₁ ℓ₂ : Level} -> Algebra ℓ₁ S -> Algebra ℓ₂ S -> Set _
Hom 𝑨 𝑩 = ∃ λ (f : ∣ 𝑨 ∣ -> ∣ 𝑩 ∣ )
  ->      (𝓸 : ∣ S ∣ ) -> (𝒂 : ⟦ S ⟧ 𝓸 -> ∣ 𝑨 ∣ )
         ---------------------------------------
  ->      f (⟦ 𝑨 ⟧ 𝓸 𝒂) ≡ ⟦ 𝑩 ⟧ 𝓸 (f ∘ 𝒂)

id : (𝑨 : Algebra k S) -> Hom 𝑨 𝑨
id (A , 𝑨) = (λ x -> x) , λ _ _ -> refl

-------------------------------------------------------------------------------
--KERNEL OF A FUNCTION
-----------------------

-- ...as a relation.
ker : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂}
  ->  (f : A -> B) -> Rel A ℓ₂
ker f x y = f x ≡ f y

-- ...as a binary predicate.
KER : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂}
  ->  (f : A -> B) -> Pred (A × A) ℓ₂
KER f (x , y) = f x ≡ f y


--Isomorphism
Iso : Algebra k S -> Algebra k S -> Set _
Iso 𝑨 𝑩 = ∃ λ (f : Hom 𝑨 𝑩)
  ->          ∃ λ (g : Hom 𝑩 𝑨)
             -----------------------------
  ->          ∣ f ∣ ∘ ∣ g ∣ ≡ ∣ id 𝑩 ∣ × ∣ g ∣ ∘ ∣ f ∣ ≡ ∣ id 𝑨 ∣

𝟎 : (A : Set k) -> Rel A k
𝟎 A a₁ a₂ = a₁ ≡ a₂


AlgebraIso : (𝑨 𝑩 : Algebra k S)
  ->           Pred (Hom 𝑨 𝑩) (lsuc k)
AlgebraIso 𝑨 𝑩  = λ f → ker ∣ f ∣ ≡ 𝟎 ∣ 𝑨 ∣

_≅_ : Rel (Algebra k S) (i ⊔ j ⊔ lsuc k)
𝑨 ≅ 𝑩 = ∃ λ (f : Hom 𝑨 𝑩) -> f ∈ AlgebraIso 𝑨 𝑩

_>>>_ : Hom 𝑨 𝑩  ->  Hom 𝑩 𝑪
        ---------------------
  ->         Hom 𝑨 𝑪
f >>> g = ∣ g ∣ ∘ ∣ f ∣ , γ
  where
    γ :  (𝓸 : ∣ S ∣ )
      -> (𝒂 : ⟦ S ⟧ 𝓸 -> ∣ 𝑨 ∣ )
         ------------------------------------------------------
      -> (∣ g ∣ ∘ ∣ f ∣ ) (⟦ 𝑨 ⟧ 𝓸 𝒂) ≡ ⟦ 𝑪 ⟧ 𝓸 (∣ g ∣ ∘ ∣ f ∣ ∘ 𝒂)
    γ 𝓸 𝒂 rewrite ⟦ f ⟧ 𝓸 𝒂 = ⟦ g ⟧ 𝓸 (∣ f ∣ ∘ 𝒂)

-- Equalizers in Alg
_~_ : Hom 𝑨 𝑩 → Hom 𝑨 𝑩 → Pred ∣ 𝑨 ∣ _
_~_ (f , _) (g , _) x = f x ≡ g x
