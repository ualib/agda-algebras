--File: Hom.agda
--Author: William DeMeo and Siva Somayyajula
--Date: 20 Feb 2020
--Updated: 23 Feb 2020

{-# OPTIONS --without-K --exact-split #-}

open import Preliminaries
open import Basic

module Hom where

private
  variable
    i j k l m : Level
    S : Signature i j


--The category of algebras Alg with morphisms as Homs
Hom : Algebra k S -> Algebra l S -> Set _
Hom {S = F , ρ} (A , 𝐹ᴬ) (B , 𝐹ᴮ) =
    ∃ λ (f : A -> B ) -> (𝓸 : F ) -> (𝒂 : ρ 𝓸 -> A )
         ---------------------------------------
  ->      f (𝐹ᴬ 𝓸 𝒂) ≡ 𝐹ᴮ 𝓸 (f ∘ 𝒂)

id : (𝑨 : Algebra k S) -> Hom 𝑨 𝑨
id (A , 𝑨) = (λ x -> x) , λ _ _ -> refl

module _ {𝑨 : Algebra k S}{𝑩 : Algebra l S}{𝑪 : Algebra m S} where

  -- Equalizers in Alg
  _~_ : Hom 𝑨 𝑩 → Hom 𝑨 𝑩 → Pred ∣ 𝑨 ∣ _
  _~_ (f , _) (g , _) x = f x ≡ g x

  --Homomorphism composition
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

-----------------------------------------------------------------
Id : {ℓ : Level}(𝑨 : Algebra ℓ S) -> Hom 𝑨 𝑨
Id 𝑨 = (λ x -> x) , λ _ _ -> refl

-----------------------------------------------------------------
--Isomorphism
_≅_[_,_] : (𝑨 : Algebra k S) -> (𝑩 : Algebra l S) -> Hom 𝑨 𝑩 -> Hom 𝑩 𝑨 -> Set (k ⊔ l)
𝑨 ≅ 𝑩 [ f , g ] = ∣ f ∣ ∘ ∣ g ∣ ≡ ∣ Id 𝑩 ∣ × ∣ g ∣ ∘ ∣ f ∣ ≡ ∣ id 𝑨 ∣

Iso : Algebra k S -> Algebra k S -> Set _
Iso 𝑨 𝑩 = ∃ λ (f : Hom 𝑨 𝑩) -> ∃ λ (g : Hom 𝑩 𝑨)
  -> ∣ f ∣ ∘ ∣ g ∣ ≡ ∣ id 𝑩 ∣ × ∣ g ∣ ∘ ∣ f ∣ ≡ ∣ id 𝑨 ∣

𝟎 : {ℓ : Level} (A : Set ℓ) -> Rel A ℓ
𝟎 A a₁ a₂ = a₁ ≡ a₂

--For algebras, isomorphisms are simply homs with 0 kernel.
AlgebraIso : (𝑨 𝑩 : Algebra k S) -> Pred (Hom 𝑨 𝑩) (lsuc k)
AlgebraIso 𝑨 𝑩  = λ f → ker ∣ f ∣ ≡ 𝟎 ∣ 𝑨 ∣

_≅_ : Rel (Algebra k S) _
𝑨 ≅ 𝑩 = ∃ λ (f : Hom 𝑨 𝑩) -> f ∈ AlgebraIso 𝑨 𝑩

_≈_ : REL (Algebra k S) (Algebra l S) _
𝑨 ≈ 𝑩 = ∃ λ (p : (Hom 𝑨 𝑩 × Hom 𝑩 𝑨)) -> 𝑨 ≅ 𝑩 [ ∣ p ∣ , ⟦ p ⟧ ]

