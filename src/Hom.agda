--File: Hom.agda
--Author: William DeMeo and Siva Somayyajula
--Date: 20 Feb 2020
--Updated: 23 Feb 2020

{-# OPTIONS --without-K --exact-split #-}

open import Preliminaries
--  using (Level; ∃; _,_; ∣_∣; _≡_; refl; _∘_; Pred)
open import Basic

module Hom {i j k : Level} {S : Signature i j} where


--The category of algebras Alg with morphisms as Homs

Hom₀ : Algebra k S -> Algebra k S -> Set _
Hom₀ (A , 𝐹ᴬ) (B , 𝐹ᴮ) =
    ∃ λ (f : A -> B) -> (𝓸 : ∣ S ∣) (𝒂 : ⟦ S ⟧ 𝓸 -> A)
     -----------------------------------------
      ->    f (𝐹ᴬ 𝓸 𝒂) ≡ 𝐹ᴮ 𝓸 (f ∘ 𝒂)

--(We need more level-generality, e.g., in Free.agda)
Hom : ∀{ℓ₁ ℓ₂ : Level}
  -> Algebra ℓ₁ S -> Algebra ℓ₂ S -> Set (i ⊔ j ⊔ ℓ₁ ⊔ ℓ₂)
Hom (A , 𝐹ᴬ) (B , 𝐹ᴮ) =
    ∃ λ (f : A -> B) -> (𝓸 : ∣ S ∣) (𝒂 : ⟦ S ⟧ 𝓸 -> A)
     -----------------------------------------
      ->    f (𝐹ᴬ 𝓸 𝒂) ≡ 𝐹ᴮ 𝓸 (f ∘ 𝒂)

id : (𝑨 : Algebra k S) -> Hom 𝑨 𝑨
id (A , 𝑨) = (λ x -> x) , λ _ _ -> refl

private
  variable
    ℓ₂ ℓ₃ : Level
    𝑨 : Algebra k S
    𝑩 : Algebra ℓ₂ S

_>>>_ : {𝑪 : Algebra ℓ₃ S}

  ->   Hom 𝑨 𝑩  ->  Hom 𝑩 𝑪
      -------------------------
  ->         Hom 𝑨 𝑪

_>>>_ {𝑨 = (A , 𝐹ᴬ)} {𝑪 = (C , 𝐹ᶜ)}
      (f , α) (g , β) = g ∘ f , γ
        where
          γ :    (𝓸 : ∣ S ∣) (𝒂 : ⟦ S ⟧ 𝓸 -> A)
               ---------------------------------------
            ->   (g ∘ f) (𝐹ᴬ 𝓸 𝒂) ≡ 𝐹ᶜ 𝓸 (g ∘ f ∘ 𝒂)
          γ 𝓸 𝒂 rewrite α 𝓸 𝒂 = β 𝓸 (f ∘ 𝒂)

-- Equalizers in Alg
_~_ : Hom 𝑨 𝑩 → Hom 𝑨 𝑩 → Pred ∣ 𝑨 ∣ _
_~_ (f , _) (g , _) x = f x ≡ g x


