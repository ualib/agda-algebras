
{-# OPTIONS --without-K --exact-split --safe #-}

open import Overture using (Signature ; 𝓞 ; 𝓥 )

module Base.Homomorphisms.Products {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive  using () renaming ( Set to Type )
open import Data.Product    using ( _,_ )
open import Level           using ( Level ;  _⊔_ ; suc )

open import Relation.Binary.PropositionalEquality using ( refl )

open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)
  using ()

open import Overture using ( ∣_∣ ; ∥_∥)

open import Base.Algebras             {𝑆 = 𝑆}  using ( Algebra ; ⨅ )
open import Base.Homomorphisms.Basic  {𝑆 = 𝑆}  using ( hom ; epi )

private variable 𝓘 β : Level

module _ {I : Type 𝓘}(ℬ : I → Algebra β) where

 ⨅-hom-co :  funext 𝓘 β → {α : Level}(𝑨 : Algebra α)
  →           (∀(i : I) → hom 𝑨 (ℬ i)) → hom 𝑨 (⨅ ℬ)

 ⨅-hom-co fe 𝑨 𝒽 = (λ a i → ∣ 𝒽 i ∣ a) , λ 𝑓 𝒶 → fe λ i → ∥ 𝒽 i ∥ 𝑓 𝒶

 ⨅-hom :  funext 𝓘 β → {α : Level}(𝒜 : I → Algebra α)
  →        (∀(i : I) → hom (𝒜 i) (ℬ i)) → hom (⨅ 𝒜)(⨅ ℬ)

 ⨅-hom fe 𝒜 𝒽 = (λ x i → ∣ 𝒽 i ∣ (x i)) , λ 𝑓 𝒶 → fe λ i → ∥ 𝒽 i ∥ 𝑓 λ x → 𝒶 x i

 ⨅-projection-hom : (i : I) → hom (⨅ ℬ) (ℬ i)
 ⨅-projection-hom = λ x → (λ z → z x) , λ _ _ → refl

