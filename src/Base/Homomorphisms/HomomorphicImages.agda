
{-# OPTIONS --without-K --exact-split --safe #-}

open import Overture using ( Signature ; 𝓞 ; 𝓥 )

module Base.Homomorphisms.HomomorphicImages {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive  using () renaming ( Set to Type )
open import Data.Product    using ( _,_ ; Σ-syntax ; Σ ; _×_ )
open import Level           using ( Level ;  _⊔_ ; suc )
open import Relation.Unary  using ( Pred ; _∈_ )
open import Relation.Binary.PropositionalEquality as ≡
                            using ( _≡_ ; module ≡-Reasoning )

open import Overture  using ( 𝑖𝑑 ; ∣_∣ ; ∥_∥ ; lower∼lift ; lift∼lower )
open import Base.Functions
                      using ( Image_∋_ ; Inv ; InvIsInverseʳ ; eq ; IsSurjective )
open import Base.Algebras {𝑆 = 𝑆}
                      using ( Algebra ; Level-of-Carrier ; Lift-Alg ; ov )

open import Base.Homomorphisms.Basic       {𝑆 = 𝑆} using ( hom ; 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇 )
open import Base.Homomorphisms.Properties  {𝑆 = 𝑆} using ( Lift-hom )

module _ {α β : Level } where

 _IsHomImageOf_ : (𝑩 : Algebra β)(𝑨 : Algebra α) → Type _
 𝑩 IsHomImageOf 𝑨 = Σ[ φ ∈ hom 𝑨 𝑩 ] IsSurjective ∣ φ ∣

 HomImages : Algebra α → Type(𝓞 ⊔ 𝓥 ⊔ α ⊔ suc β)
 HomImages 𝑨 = Σ[ 𝑩 ∈ Algebra β ] 𝑩 IsHomImageOf 𝑨

module _ {α : Level} where

 IsHomImageOfClass : {𝒦 : Pred (Algebra α)(suc α)} → Algebra α → Type(ov α)
 IsHomImageOfClass {𝒦 = 𝒦} 𝑩 = Σ[ 𝑨 ∈ Algebra α ] ((𝑨 ∈ 𝒦) × (𝑩 IsHomImageOf 𝑨))

 HomImageOfClass : Pred (Algebra α) (suc α) → Type(ov α)
 HomImageOfClass 𝒦 = Σ[ 𝑩 ∈ Algebra α ] IsHomImageOfClass{𝒦} 𝑩

module _ {α β : Level} where

 open Level
 open ≡-Reasoning

 Lift-epi-is-epi :  {𝑨 : Algebra α}(ℓᵃ : Level){𝑩 : Algebra β}(ℓᵇ : Level)(h : hom 𝑨 𝑩)
  →                 IsSurjective ∣ h ∣ → IsSurjective ∣ Lift-hom ℓᵃ {𝑩} ℓᵇ h ∣

 Lift-epi-is-epi {𝑨 = 𝑨} ℓᵃ {𝑩} ℓᵇ h hepi y = eq (lift a) η
  where
   lh : hom (Lift-Alg 𝑨 ℓᵃ) (Lift-Alg 𝑩 ℓᵇ)
   lh = Lift-hom ℓᵃ {𝑩} ℓᵇ h

   ζ : Image ∣ h ∣ ∋ (lower y)
   ζ = hepi (lower y)

   a : ∣ 𝑨 ∣
   a = Inv ∣ h ∣ ζ

   ν : lift (∣ h ∣ a) ≡ ∣ Lift-hom ℓᵃ {𝑩} ℓᵇ h ∣ (Level.lift a)
   ν = ≡.cong (λ - → lift (∣ h ∣ (- a))) (lower∼lift {Level-of-Carrier 𝑨}{β})

   η :  y ≡ ∣ lh ∣ (lift a)
   η =  y                ≡⟨ (≡.cong-app lift∼lower) y              ⟩
        lift (lower y)   ≡⟨ ≡.cong lift (≡.sym (InvIsInverseʳ ζ))  ⟩
        lift (∣ h ∣ a)   ≡⟨ ν                                      ⟩
        ∣ lh ∣ (lift a)  ∎

 Lift-Alg-hom-image :  {𝑨 : Algebra α}(ℓᵃ : Level){𝑩 : Algebra β}(ℓᵇ : Level)
  →                    𝑩 IsHomImageOf 𝑨
  →                    (Lift-Alg 𝑩 ℓᵇ) IsHomImageOf (Lift-Alg 𝑨 ℓᵃ)

 Lift-Alg-hom-image {𝑨 = 𝑨} ℓᵃ {𝑩} ℓᵇ ((φ , φhom) , φepic) = Goal
  where
  lφ : hom (Lift-Alg 𝑨 ℓᵃ) (Lift-Alg 𝑩 ℓᵇ)
  lφ = Lift-hom ℓᵃ {𝑩} ℓᵇ (φ , φhom)

  lφepic : IsSurjective ∣ lφ ∣
  lφepic = Lift-epi-is-epi ℓᵃ {𝑩} ℓᵇ (φ , φhom) φepic
  Goal : (Lift-Alg 𝑩 ℓᵇ) IsHomImageOf _
  Goal = lφ , lφepic

