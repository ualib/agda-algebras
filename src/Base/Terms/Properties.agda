
{-# OPTIONS --without-K --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Base.Terms.Properties {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive          using () renaming ( Set to Type )
open import Data.Product            using ( _,_ ; Σ-syntax )
open import Function                using ( _∘_ )
open import Data.Empty.Polymorphic  using ( ⊥ )
open import Level                   using ( Level )
open import Relation.Binary         using ( IsEquivalence ; Setoid ; Reflexive )
                                    using ( Symmetric ; Transitive )
open import Relation.Binary.PropositionalEquality as ≡
                                    using ( _≡_ ; module ≡-Reasoning )
open import Axiom.Extensionality.Propositional
                                    using () renaming (Extensionality to funext)

open import Overture                using ( _⁻¹ ; 𝑖𝑑 ; ∣_∣ ; ∥_∥ )
open import Base.Functions          using ( Inv ; InvIsInverseʳ ; Image_∋_)
                                    using ( eq ; IsSurjective )
open  import Base.Equality          using ( swelldef )

open  import Base.Algebras       {𝑆 = 𝑆} using ( Algebra ; _̂_  ; ov )
open  import Base.Homomorphisms  {𝑆 = 𝑆} using ( hom )
open  import Base.Terms.Basic    {𝑆 = 𝑆} using ( Term ; 𝑻 )

open Term
private variable α β χ : Level

private variable X : Type χ

free-lift : (𝑨 : Algebra α)(h : X → ∣ 𝑨 ∣) → ∣ 𝑻 X ∣ → ∣ 𝑨 ∣
free-lift _ h (ℊ x) = h x
free-lift 𝑨 h (node f 𝑡) = (f ̂ 𝑨) (λ i → free-lift 𝑨 h (𝑡 i))

lift-hom : (𝑨 : Algebra α) → (X → ∣ 𝑨 ∣) → hom (𝑻 X) 𝑨
lift-hom 𝑨 h = free-lift 𝑨 h , λ f a → ≡.cong (f ̂ 𝑨) ≡.refl

open ≡-Reasoning

free-unique :  swelldef 𝓥 α → (𝑨 : Algebra α)(g h : hom (𝑻 X) 𝑨)
 →             (∀ x → ∣ g ∣ (ℊ x) ≡ ∣ h ∣ (ℊ x))
 →             ∀(t : Term X) →  ∣ g ∣ t ≡ ∣ h ∣ t

free-unique _ _ _ _ p (ℊ x) = p x

free-unique wd 𝑨 g h p (node 𝑓 𝑡) =
 ∣ g ∣ (node 𝑓 𝑡)    ≡⟨ ∥ g ∥ 𝑓 𝑡 ⟩
 (𝑓 ̂ 𝑨)(∣ g ∣ ∘ 𝑡)  ≡⟨ Goal ⟩
 (𝑓 ̂ 𝑨)(∣ h ∣ ∘ 𝑡)  ≡⟨ (∥ h ∥ 𝑓 𝑡)⁻¹ ⟩
 ∣ h ∣ (node 𝑓 𝑡)    ∎
  where
  Goal : (𝑓 ̂ 𝑨) (λ x → ∣ g ∣ (𝑡 x)) ≡ (𝑓 ̂ 𝑨) (λ x → ∣ h ∣ (𝑡 x))
  Goal = wd (𝑓 ̂ 𝑨)(∣ g ∣ ∘ 𝑡)(∣ h ∣ ∘ 𝑡)(λ i → free-unique wd 𝑨 g h p (𝑡 i))

lift-of-epi-is-epi :  (𝑨 : Algebra α){h₀ : X → ∣ 𝑨 ∣}
 →                    IsSurjective h₀ → IsSurjective ∣ lift-hom 𝑨 h₀ ∣

lift-of-epi-is-epi 𝑨 {h₀} hE y = Goal
 where
 h₀⁻¹y = Inv h₀ (hE y)

 η : y ≡ ∣ lift-hom 𝑨 h₀ ∣ (ℊ h₀⁻¹y)
 η = (InvIsInverseʳ (hE y))⁻¹

 Goal : Image ∣ lift-hom 𝑨 h₀ ∣ ∋ y
 Goal = eq (ℊ h₀⁻¹y) η

