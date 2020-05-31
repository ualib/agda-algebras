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

--There are two levels of intesionality.
--  1. partial intensionality (intensional with respect to 𝒂, but extensional with respect to 𝓸).
--  intensional preservation of operations
op_interpreted-in_and_commutes-intensionally-with : (𝓸 : ∣ S ∣ ) (𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓦 S) (f : ∣ 𝑨 ∣  → ∣ 𝑩 ∣ ) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
op 𝓸 interpreted-in 𝑨 and 𝑩 commutes-intensionally-with f = (λ 𝒂 → f (∥ 𝑨 ∥ 𝓸 𝒂) ) ≡ (λ 𝒂 → ∥ 𝑩 ∥ 𝓸 (f ∘ 𝒂) )
     --(The implicit typing judgment here is `𝒂 : ∥ S ∥ 𝓸 → ∣ 𝑨 ∣`, which represents an (∥ S ∥ 𝓸)-tuple of elements from ∣ 𝑨 ∣.)

all-ops-in_and_commute-partially-intensionally-with : (𝑨 : Algebra 𝓤 S)(𝑩 : Algebra 𝓦 S)( f : ∣ 𝑨 ∣  → ∣ 𝑩 ∣ ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
all-ops-in 𝑨 and 𝑩 commute-partially-intensionally-with f = ∀  (𝓸 : ∣ S ∣ ) → op 𝓸 interpreted-in 𝑨 and 𝑩 commutes-intensionally-with f

intensional-hom : (𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓦 S) → ( ∣ 𝑨 ∣ → ∣ 𝑩 ∣ ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
intensional-hom 𝑨 𝑩 f = all-ops-in 𝑨 and 𝑩 commute-partially-intensionally-with f

Hom : Algebra 𝓤 S → Algebra 𝓦 S  → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
Hom 𝑨 𝑩 = Σ f ꞉ ( ∣ 𝑨 ∣ → ∣ 𝑩 ∣ ) , all-ops-in 𝑨 and 𝑩 commute-partially-intensionally-with f

--  2. full intensionality (intensional with respect to both 𝓸 and 𝒂)
preserves-ops : (𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓦 S) → (∣ 𝑨 ∣  → ∣ 𝑩 ∣ ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
preserves-ops (A , 𝐹ᴬ)  (B , 𝐹ᴮ) f = (λ (𝓸 : ∣ S ∣ ) ( 𝒂 : ∥ S ∥ 𝓸 → A )  → f (𝐹ᴬ 𝓸 𝒂) ) ≡ (λ (𝓸 : ∣ S ∣ ) ( 𝒂 : ∥ S ∥ 𝓸 → A )  → 𝐹ᴮ 𝓸 (f ∘ 𝒂) )
all-ops-in_and_commute-intensionally-with : (𝑨 : Algebra 𝓤 S)(𝑩 : Algebra 𝓦 S)( f : ∣ 𝑨 ∣  → ∣ 𝑩 ∣ ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
all-ops-in 𝑨 and 𝑩 commute-intensionally-with f = preserves-ops 𝑨 𝑩 f

--the type of (intensional) homomorphisms
HOM : Algebra 𝓤 S → Algebra 𝓦 S  → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
HOM 𝑨 𝑩 = Σ f ꞉ ( ∣ 𝑨 ∣ → ∣ 𝑩 ∣ ) , all-ops-in 𝑨 and 𝑩 commute-intensionally-with f

--extensional preservation of operations
op_interpreted-in_and_commutes-extensionally-with : (𝓸 : ∣ S ∣ ) (𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓦 S) (f : ∣ 𝑨 ∣  → ∣ 𝑩 ∣ ) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
op 𝓸 interpreted-in 𝑨 and 𝑩 commutes-extensionally-with  f = ∀( 𝒂 : ∥ S ∥ 𝓸 → ∣ 𝑨 ∣ )  → f (∥ 𝑨 ∥ 𝓸 𝒂) ≡ ∥ 𝑩 ∥ 𝓸 (f ∘ 𝒂)

all-ops-in_and_commute-extensionally-with : (𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓦 S) → (∣ 𝑨 ∣  → ∣ 𝑩 ∣ ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
all-ops-in 𝑨 and 𝑩 commute-extensionally-with f =  ∀ (𝓸 : ∣ S ∣ ) → op 𝓸 interpreted-in 𝑨 and 𝑩 commutes-extensionally-with f

is-homomorphism : (𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓦 S) → ( ∣ 𝑨 ∣ → ∣ 𝑩 ∣ ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
is-homomorphism 𝑨 𝑩 f = all-ops-in 𝑨 and 𝑩 commute-extensionally-with f

--the type of (extensional) homomorphisms
hom : Algebra 𝓤 S → Algebra 𝓦 S  → 𝓤 ⊔ 𝓦 ⊔ 𝓥 ⊔ 𝓞 ̇
--Hom  (A , 𝐹ᴬ)  (B , 𝐹ᴮ) = Σ f ꞉ (A → B) , ( (𝓸 : ∣ S ∣ ) → ( 𝒂 : ∥ S ∥ 𝓸 → A )  → f (𝐹ᴬ 𝓸 𝒂) ≡ 𝐹ᴮ 𝓸 (f ∘ 𝒂) )
hom 𝑨 𝑩 = Σ f ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣ ) , is-homomorphism 𝑨 𝑩 f

𝓲𝓭 :  (A : Algebra 𝓤 S) → hom A A
𝓲𝓭 _ = (λ x → x) , λ _ _ → refl _

module _ {A : Algebra 𝓤 S} {B : Algebra 𝓦 S} {C : Algebra 𝓣 S} where

  --homomorphism composition
  _>>>_ : hom A B  → hom B C
              ---------------------
    →             hom A C
  (f , fhom) >>> (g , ghom) = g ∘ f , γ
    where
      γ :      (𝓸 : ∣ S ∣ ) → ( 𝒂 : ∥ S ∥ 𝓸 → ∣ A ∣ )
             -------------------------------------------------
       →   ( g ∘ f ) ( ∥ A ∥ 𝓸 𝒂 )  ≡  ∥ C ∥ 𝓸 ( g ∘ f ∘ 𝒂)
      γ 𝓸 𝒂  =   ( g ∘ f ) (∥ A ∥ 𝓸 𝒂)     ≡⟨ ap (λ - → g -) (fhom 𝓸 𝒂) ⟩
                      g  ( ∥ B ∥ 𝓸 ( f ∘ 𝒂 ) )  ≡⟨ ghom 𝓸 ( f ∘ 𝒂 ) ⟩
                      ∥ C ∥ 𝓸 ( g ∘ f ∘ 𝒂)     ∎

-- Equalizers in Alg
𝓔 : {A : Algebra 𝓤 S} {B : Algebra 𝓦 S} → hom A B → hom A B → 𝓤 ⊔ 𝓦 ̇
𝓔 (f , _) (g , _) = Σ x ꞉ _ , f x ≡ g x

--Isomorphism
_≅_ : (A B : Algebra 𝓤 S) → 𝓤 ⊔ 𝓞 ⊔ 𝓥 ̇
A ≅ B =  Σ f ꞉ (hom A B) ,   Σ g ꞉ (hom B A) ,
             ( ∣ f ∣ ∘ ∣ g ∣ ≡ ∣ 𝓲𝓭 B ∣ )   ×   ( ∣ g ∣ ∘ ∣ f ∣ ≡ ∣ 𝓲𝓭 A ∣ )

  --For algebras, isomorphisms are simply homs with 0 kernel.
is-algebra-iso : {A B : Algebra 𝓤 S} (f : hom A B) → 𝓤 ⁺ ̇
is-algebra-iso {𝓤}{A} f =  ker ∣ f ∣ ≡ 𝟎 {𝓤}{∣ A ∣}

AlgebraIsos : (A B : Algebra 𝓤 S) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
AlgebraIsos {𝓤} A B = Σ f ꞉ (hom A B) , is-algebra-iso {𝓤} {A} {B} f

_≈_ : Rel (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
A ≈ B = is-singleton (AlgebraIsos A B)

-- _≈_ : REL (Algebra k S) (Algebra l S) _
-- 𝑨 ≈ 𝑩 = ∃ λ (p : (hom 𝑨 𝑩 × hom 𝑩 𝑨)) -> 𝑨 ≅ 𝑩 [ ∣ p ∣ , ⟦ p ⟧ ]

