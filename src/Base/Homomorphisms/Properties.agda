
{-# OPTIONS --without-K --exact-split --safe #-}

open import Overture using (Signature ; 𝓞 ; 𝓥 )

module Base.Homomorphisms.Properties {𝑆 : Signature 𝓞 𝓥} where

open import Data.Product  using ( _,_ )
open import Function      using ( _∘_ )
open import Level         using ( Level )

open  import Relation.Binary.PropositionalEquality as ≡
      using ( _≡_ ; module ≡-Reasoning )

open import Overture                           using ( ∣_∣ ; ∥_∥ )
open import Base.Algebras             {𝑆 = 𝑆}  using ( Algebra ; _̂_ ; Lift-Alg )
open import Base.Homomorphisms.Basic  {𝑆 = 𝑆}  using ( hom ; is-homomorphism )

private variable α β γ ρ : Level

open ≡-Reasoning

module _ (𝑨 : Algebra α){𝑩 : Algebra β}(𝑪 : Algebra γ) where

  ∘-hom : hom 𝑨 𝑩  →  hom 𝑩 𝑪  →  hom 𝑨 𝑪
  ∘-hom (g , ghom) (h , hhom) = h ∘ g , Goal where

   Goal : ∀ 𝑓 a → (h ∘ g)((𝑓 ̂ 𝑨) a) ≡ (𝑓 ̂ 𝑪)(h ∘ g ∘ a)
   Goal 𝑓 a =  (h ∘ g)((𝑓 ̂ 𝑨) a)  ≡⟨ ≡.cong h ( ghom 𝑓 a )  ⟩
               h ((𝑓 ̂ 𝑩)(g ∘ a))  ≡⟨ hhom 𝑓 ( g ∘ a )       ⟩
               (𝑓 ̂ 𝑪)(h ∘ g ∘ a)  ∎

  ∘-is-hom :  {f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣}{g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣}
   →          is-homomorphism 𝑨 𝑩 f → is-homomorphism 𝑩 𝑪 g
   →          is-homomorphism 𝑨 𝑪 (g ∘ f)

  ∘-is-hom {f} {g} fhom ghom = ∥ ∘-hom (f , fhom) (g , ghom) ∥

open Level

Lift-hom :  {𝑨 : Algebra α}(ℓᵃ : Level){𝑩 : Algebra β} (ℓᵇ : Level)
 →          hom 𝑨 𝑩  →  hom (Lift-Alg 𝑨 ℓᵃ) (Lift-Alg 𝑩 ℓᵇ)

Lift-hom {𝑨 = 𝑨} ℓᵃ {𝑩} ℓᵇ (f , fhom) = lift ∘ f ∘ lower , Goal
 where
 lABh : is-homomorphism (Lift-Alg 𝑨 ℓᵃ) 𝑩 (f ∘ lower)
 lABh = ∘-is-hom (Lift-Alg 𝑨 ℓᵃ) 𝑩 {lower}{f} (λ _ _ → ≡.refl) fhom

 Goal : is-homomorphism(Lift-Alg 𝑨 ℓᵃ)(Lift-Alg 𝑩 ℓᵇ) (lift ∘ (f ∘ lower))
 Goal = ∘-is-hom  (Lift-Alg 𝑨 ℓᵃ) (Lift-Alg 𝑩 ℓᵇ)
                  {f ∘ lower}{lift} lABh λ _ _ → ≡.refl

