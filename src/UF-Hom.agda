--File: UF-Hom.agda
--Author: William DeMeo and Siva Somayyajula
--Date: 20 Feb 2020
--Updated: 22 Apr 2020

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-Prelude using (𝓡; 𝓢; 𝓣; 𝓤; 𝓤₀;𝓥; 𝓦; 𝓞; _⁺; _̇;_⊔_; _,_; Σ; -Σ; ∣_∣; ∥_∥; _≡_; refl; _∼_; _≡⟨_⟩_; _∎; ap; _⁻¹; _∘_; _×_)
open import UF-Basic using (Signature; Algebra)
open import UF-Rel using (ker; Rel)
open import UF-Con using (𝟎)
open import UF-Singleton using (is-singleton)

module UF-Hom {S : Signature 𝓞 𝓥} where

preserves-ops : (𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓦 S) → (∣ 𝑨 ∣  → ∣ 𝑩 ∣ ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
preserves-ops (A , 𝐹ᴬ)  (B , 𝐹ᴮ) f = (λ (𝓸 : ∣ S ∣ ) ( 𝒂 : ∥ S ∥ 𝓸 → A )  → f (𝐹ᴬ 𝓸 𝒂) ) ≡ (λ (𝓸 : ∣ S ∣ ) ( 𝒂 : ∥ S ∥ 𝓸 → A )  → 𝐹ᴮ 𝓸 (f ∘ 𝒂) )

is-homomorphism : (𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓦 S) → ( ∣ 𝑨 ∣ → ∣ 𝑩 ∣ ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
is-homomorphism 𝑨 𝑩 f = preserves-ops 𝑨 𝑩 f

Hom : Algebra 𝓤 S → Algebra 𝓦 S  → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
Hom 𝑨 𝑩 = Σ f ꞉ ( ∣ 𝑨 ∣ → ∣ 𝑩 ∣ ) , preserves-ops 𝑨 𝑩 f

--EXT (extensional versions)
preserves-ops-EXT : (𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓦 S) → (∣ 𝑨 ∣  → ∣ 𝑩 ∣ ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
preserves-ops-EXT (A , 𝐹ᴬ)  (B , 𝐹ᴮ) f = ( (𝓸 : ∣ S ∣ ) → ( 𝒂 : ∥ S ∥ 𝓸 → A )  → f (𝐹ᴬ 𝓸 𝒂) ≡ 𝐹ᴮ 𝓸 (f ∘ 𝒂) )

is-hom-EXT : (𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓦 S) → ( ∣ 𝑨 ∣ → ∣ 𝑩 ∣ ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
is-hom-EXT 𝑨 𝑩 f = preserves-ops-EXT 𝑨 𝑩 f

Hom-EXT : Algebra 𝓤 S → Algebra 𝓦 S  → 𝓤 ⊔ 𝓦 ⊔ 𝓥 ⊔ 𝓞 ̇
Hom-EXT  (A , 𝐹ᴬ)  (B , 𝐹ᴮ) = Σ f ꞉ (A → B) , ( (𝓸 : ∣ S ∣ ) → ( 𝒂 : ∥ S ∥ 𝓸 → A )  → f (𝐹ᴬ 𝓸 𝒂) ≡ 𝐹ᴮ 𝓸 (f ∘ 𝒂) )


𝓲𝓭 :  (A : Algebra 𝓤 S) → Hom-EXT A A
𝓲𝓭 _ = (λ x → x) , λ _ _ → refl _

module _ {A : Algebra 𝓤 S} {B : Algebra 𝓦 S} {C : Algebra 𝓣 S} where

  --Homomorphism composition
  _>>>_ : Hom-EXT A B  → Hom-EXT B C
              ---------------------
    →             Hom-EXT A C
  (f , fhom) >>> (g , ghom) = g ∘ f , γ
    where
      γ :      (𝓸 : ∣ S ∣ ) → ( 𝒂 : ∥ S ∥ 𝓸 → ∣ A ∣ )
             -------------------------------------------------
       →   ( g ∘ f ) ( ∥ A ∥ 𝓸 𝒂 )  ≡  ∥ C ∥ 𝓸 ( g ∘ f ∘ 𝒂)
      γ 𝓸 𝒂  =   ( g ∘ f ) (∥ A ∥ 𝓸 𝒂)     ≡⟨ ap (λ - → g -) (fhom 𝓸 𝒂) ⟩
                      g  ( ∥ B ∥ 𝓸 ( f ∘ 𝒂 ) )  ≡⟨ ghom 𝓸 ( f ∘ 𝒂 ) ⟩
                      ∥ C ∥ 𝓸 ( g ∘ f ∘ 𝒂)     ∎

-- Equalizers in Alg
𝓔 : {A : Algebra 𝓤 S} {B : Algebra 𝓦 S} → Hom A B → Hom A B → 𝓤 ⊔ 𝓦 ̇
𝓔 (f , _) (g , _) = Σ x ꞉ _ , f x ≡ g x

--Isomorphism
_≅_ : (A B : Algebra 𝓤 S) → 𝓤 ⊔ 𝓞 ⊔ 𝓥 ̇
A ≅ B =  Σ f ꞉ (Hom A B) ,   Σ g ꞉ (Hom B A) ,
             ( ∣ f ∣ ∘ ∣ g ∣ ≡ ∣ 𝓲𝓭 B ∣ )   ×   ( ∣ g ∣ ∘ ∣ f ∣ ≡ ∣ 𝓲𝓭 A ∣ )

  --For algebras, isomorphisms are simply homs with 0 kernel.
is-algebra-iso : {A B : Algebra 𝓤 S} (f : Hom A B) → 𝓤 ⁺ ̇
is-algebra-iso {𝓤}{A} f =  ker ∣ f ∣ ≡ 𝟎 {𝓤}{∣ A ∣}

AlgebraIsos : (A B : Algebra 𝓤 S) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
AlgebraIsos {𝓤} A B = Σ f ꞉ (Hom A B) , is-algebra-iso {𝓤} {A} {B} f

_≈_ : Rel (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
A ≈ B = is-singleton (AlgebraIsos A B)

-- _≈_ : REL (Algebra k S) (Algebra l S) _
-- 𝑨 ≈ 𝑩 = ∃ λ (p : (Hom 𝑨 𝑩 × Hom 𝑩 𝑨)) -> 𝑨 ≅ 𝑩 [ ∣ p ∣ , ⟦ p ⟧ ]

