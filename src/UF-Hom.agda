--File: UF-Hom.agda
--Author: William DeMeo and Siva Somayyajula
--Date: 20 Feb 2020
--Updated: 22 Apr 2020

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-Prelude using (𝓡; 𝓢; 𝓣; 𝓤; 𝓤₀;𝓥; 𝓦; 𝓞; _⁺; _̇;_⊔_; _,_; Σ; -Σ; ∣_∣; ∥_∥; _≡_; refl; _∼_; _≡⟨_⟩_; _∎; ap; _⁻¹; _∘_; _×_)
open import UF-Basic using (Signature; Algebra) -- ; Π')

module UF-Hom where


--The category of algebras Alg with morphisms as Homs
Hom : {S : Signature 𝓞 𝓥} → Algebra 𝓤 S -> Algebra 𝓦 S  → 𝓤 ⊔ 𝓦 ⊔ 𝓥 ⊔ 𝓞 ̇
Hom {S = F , ρ} (A , 𝐹ᴬ) (B , 𝐹ᴮ) = Σ f ꞉ (A → B) ,
  ( (𝓸 : F ) → ( 𝒂 : ρ 𝓸 → A )  → f (𝐹ᴬ 𝓸 𝒂) ≡ 𝐹ᴮ 𝓸 (f ∘ 𝒂) )

𝓲𝓭 : {S : Signature 𝓞 𝓥} (A : Algebra 𝓤 S) → Hom A A
𝓲𝓭 _ = (λ x -> x) , λ _ _ -> refl _

module _ {S : Signature 𝓞 𝓥} {A : Algebra 𝓤 S} {B : Algebra 𝓦 S} {C : Algebra 𝓣 S} where

-- Equalizers in Alg
  _~_ : Hom A B → Hom A B → 𝓤 ⊔ 𝓦 ̇
  _~_ (f , _) (g , _) = Σ x ꞉ ∣ A ∣ , f x ≡ g x

  --Homomorphism composition
  _>>>_ : Hom A B  → Hom B C
              ---------------------
    →             Hom A C
  (f , fhom) >>> (g , ghom) = g ∘ f , γ
    where
      γ :      (𝓸 : ∣ S ∣ ) → ( 𝒂 : ∥ S ∥ 𝓸 → ∣ A ∣ )
             -------------------------------------------------
       →   ( g ∘ f ) ( ∥ A ∥ 𝓸 𝒂 )  ≡  ∥ C ∥ 𝓸 ( g ∘ f ∘ 𝒂)
      γ 𝓸 𝒂  =   ( g ∘ f ) (∥ A ∥ 𝓸 𝒂)     ≡⟨ ap (λ - → g -) (fhom 𝓸 𝒂) ⟩
                      g  ( ∥ B ∥ 𝓸 ( f ∘ 𝒂 ) )  ≡⟨ ghom 𝓸 ( f ∘ 𝒂 ) ⟩
                      ∥ C ∥ 𝓸 ( g ∘ f ∘ 𝒂)     ∎

-----------------------------------------------------------------
--Isomorphism
-- _≅[_]_ : (𝑨 : Algebra 𝓤 S) → Hom A B → Hom 𝑩 𝑨 -> Set (k ⊔ l)
-- 𝑨 ≅[ f ] 𝑩  = ∣ f ∣ ∘ ∣ g ∣ ≡ ∣ Id 𝑩 ∣ × ∣ g ∣ ∘ ∣ f ∣ ≡ ∣ id 𝑨 ∣

_≅_ : {S : Signature 𝓞 𝓥} (A : Algebra 𝓤 S) (B : Algebra 𝓦 S) → 𝓤 ⊔ 𝓦 ⊔ 𝓞 ⊔ 𝓥 ̇
A ≅ B =  Σ f ꞉ (Hom A B) ,   Σ g ꞉ (Hom B A) ,
             ( ∣ f ∣ ∘ ∣ g ∣ ≡ ∣ 𝓲𝓭 B ∣ )   ×   ( ∣ g ∣ ∘ ∣ f ∣ ≡ ∣ 𝓲𝓭 A ∣ )

Iso : {S : Signature 𝓞 𝓥} (A : Algebra 𝓤 S) (B : Algebra 𝓦 S) → 𝓤 ⊔ 𝓦 ⊔ 𝓞 ⊔ 𝓥 ̇
Iso A B = A ≅ B -- alias

-- 𝟎 : {ℓ : Level} (A : Set ℓ) -> Rel A ℓ
-- 𝟎 A a₁ a₂ = a₁ ≡ a₂

-- --For algebras, isomorphisms are simply homs with 0 kernel.
-- AlgebraIso : (𝑨 𝑩 : Algebra k S) -> Pred (Hom 𝑨 𝑩) (lsuc k)
-- AlgebraIso 𝑨 𝑩  = λ f → ker ∣ f ∣ ≡ 𝟎 ∣ 𝑨 ∣

-- _≅_ : Rel (Algebra k S) _
-- 𝑨 ≅ 𝑩 = ∃ λ (f : Hom 𝑨 𝑩) -> f ∈ AlgebraIso 𝑨 𝑩

-- _≈_ : REL (Algebra k S) (Algebra l S) _
-- 𝑨 ≈ 𝑩 = ∃ λ (p : (Hom 𝑨 𝑩 × Hom 𝑩 𝑨)) -> 𝑨 ≅ 𝑩 [ ∣ p ∣ , ⟦ p ⟧ ]

