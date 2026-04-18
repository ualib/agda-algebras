
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Base.Homomorphisms.Factor {𝑆 : Signature 𝓞 𝓥} where

open import Data.Product    using ( Σ-syntax ; _,_ )
                            renaming ( proj₁ to fst ; proj₂ to snd )
open import Function        using ( _∘_ )
open import Level           using ( Level )
open import Relation.Unary  using ( _⊆_ )

open  import Relation.Binary.PropositionalEquality as ≡
      using ( module ≡-Reasoning ; _≡_ )

open import Overture        using ( ∣_∣ ; ∥_∥ ; _⁻¹ )
open import Base.Equality   using ( swelldef )
open import Base.Relations  using ( kernel )
open import Base.Functions  using ( IsSurjective ; SurjInv )
                            using ( SurjInvIsInverseʳ ; epic-factor )

open import Base.Algebras             {𝑆 = 𝑆}  using ( Algebra ; _̂_)
open import Base.Homomorphisms.Basic  {𝑆 = 𝑆}  using ( hom ; epi )

private variable α β γ : Level

module _ {𝑨 : Algebra α}{𝑪 : Algebra γ} where

 open ≡-Reasoning

 HomFactor :  swelldef 𝓥 γ
  →           (𝑩 : Algebra β)(τ : hom 𝑨 𝑩)(ν : hom 𝑨 𝑪)
  →           kernel ∣ ν ∣ ⊆ kernel ∣ τ ∣ → IsSurjective ∣ ν ∣
  →           Σ[ φ ∈ (hom 𝑪 𝑩)] ∀ x → ∣ τ ∣ x ≡ ∣ φ ∣ (∣ ν ∣ x)

 HomFactor wd 𝑩 τ ν Kντ νE = (φ , φIsHomCB) , τφν
  where
   νInv : ∣ 𝑪 ∣ → ∣ 𝑨 ∣
   νInv = SurjInv ∣ ν ∣ νE

   η : ∀ c → ∣ ν ∣ (νInv c) ≡ c
   η c = SurjInvIsInverseʳ ∣ ν ∣ νE c

   φ : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
   φ = ∣ τ ∣ ∘ νInv

   ξ : ∀ a → kernel ∣ ν ∣ (a , νInv (∣ ν ∣ a))
   ξ a = (η (∣ ν ∣ a))⁻¹

   τφν : ∀ x → ∣ τ ∣ x ≡ φ (∣ ν ∣ x)
   τφν = λ x → Kντ (ξ x)

   φIsHomCB : ∀ 𝑓 c → φ ((𝑓 ̂ 𝑪) c) ≡ ((𝑓 ̂ 𝑩)(φ ∘ c))
   φIsHomCB 𝑓 c =
    φ ((𝑓 ̂ 𝑪) c)                    ≡⟨ goal ⟩
    φ ((𝑓 ̂ 𝑪)(∣ ν ∣ ∘(νInv ∘ c)))   ≡⟨ ≡.cong φ (∥ ν ∥ 𝑓 (νInv ∘ c))⁻¹ ⟩
    φ (∣ ν ∣((𝑓 ̂ 𝑨)(νInv ∘ c)))     ≡⟨ (τφν ((𝑓 ̂ 𝑨)(νInv ∘ c)))⁻¹ ⟩
    ∣ τ ∣((𝑓 ̂ 𝑨)(νInv ∘ c))         ≡⟨ ∥ τ ∥ 𝑓 (νInv ∘ c) ⟩
    (𝑓 ̂ 𝑩)(λ x → ∣ τ ∣(νInv (c x))) ∎
     where
     goal : φ ((𝑓 ̂ 𝑪) c) ≡ φ ((𝑓 ̂ 𝑪) (∣ ν ∣ ∘(νInv ∘ c)))
     goal = ≡.cong φ (wd (𝑓 ̂ 𝑪) c (∣ ν ∣ ∘ (νInv ∘ c)) λ i → (η (c i))⁻¹)

 HomFactorEpi :  swelldef 𝓥 γ
  →              (𝑩 : Algebra β)(τ : hom 𝑨 𝑩)(ν : hom 𝑨 𝑪)
  →              kernel ∣ ν ∣ ⊆ kernel ∣ τ ∣
  →              IsSurjective ∣ ν ∣ → IsSurjective ∣ τ ∣
  →              Σ[ φ ∈ epi 𝑪 𝑩 ] ∀ x → ∣ τ ∣ x ≡ ∣ φ ∣ (∣ ν ∣ x)

 HomFactorEpi wd 𝑩 τ ν kerincl νe τe = (fst ∣ φF ∣ ,(snd ∣ φF ∣ , φE)), ∥ φF ∥
  where
   φF : Σ[ φ ∈ hom 𝑪 𝑩 ] ∀ x → ∣ τ ∣ x ≡ ∣ φ ∣ (∣ ν ∣ x)
   φF = HomFactor wd 𝑩 τ ν kerincl νe

   φ : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
   φ = ∣ τ ∣ ∘ (SurjInv ∣ ν ∣ νe)

   φE : IsSurjective φ
   φE = epic-factor ∣ τ ∣ ∣ ν ∣ φ ∥ φF ∥ τe

