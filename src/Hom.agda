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
    𝑨 : Algebra k S
    𝑩 : Algebra l S
    𝑪 : Algebra m S

--The category of algebras Alg with morphisms as Homs
Hom : Algebra k S -> Algebra l S -> Set _
Hom {S = F , ρ} (A , 𝐹ᴬ) (B , 𝐹ᴮ) =
    ∃ λ (f : A -> B) -> (𝓸 : F) (𝒂 : ρ 𝓸 -> A)
     -----------------------------------------
      ->    f (𝐹ᴬ 𝓸 𝒂) ≡ 𝐹ᴮ 𝓸 (f ∘ 𝒂)

id : (𝑨 : Algebra k S) -> Hom 𝑨 𝑨
id (A , 𝑨) = (λ x -> x) , λ _ _ -> refl

_>>>_ : {S : Signature i j} {𝑨 : Algebra k S}
        {𝑩 : Algebra l S} {𝑪 : Algebra m S}
  ->    Hom 𝑨 𝑩  ->  Hom 𝑩 𝑪
        ---------------------
  ->         Hom 𝑨 𝑪
_>>>_ {S = F , ρ} {𝑨 = A , 𝐹ᴬ} {𝑪 = C , 𝐹ᶜ}
      (f , α) (g , β) = g ∘ f , γ
        where
        γ :    (𝓸 : F) (𝒂 : ρ 𝓸 -> A)
             ---------------------------------------
          ->   (g ∘ f) (𝐹ᴬ 𝓸 𝒂) ≡ 𝐹ᶜ 𝓸 (g ∘ f ∘ 𝒂)
        γ 𝓸 𝒂 rewrite α 𝓸 𝒂 = β 𝓸 (f ∘ 𝒂)

-- Equalizers in Alg
_~_ : Hom 𝑨 𝑩 → Hom 𝑨 𝑩 → Pred ∣ 𝑨 ∣ _
_~_ (f , _) (g , _) x = f x ≡ g x
