
{-# OPTIONS --without-K --exact-split --safe #-}

open import Overture using ( Signature; 𝓞 ; 𝓥 )

module Base.Homomorphisms.Kernels {𝑆 : Signature 𝓞 𝓥} where

open import Data.Product   using ( _,_ )
open import Function.Base  using ( _∘_ )
open import Level          using ( Level ; _⊔_ ; suc )

open  import Relation.Binary.PropositionalEquality
      using ( _≡_ ; module ≡-Reasoning ; refl )

open import Overture        using ( ∣_∣ ; ∥_∥ ; _⁻¹ )
open import Base.Functions  using ( Image_∋_ ; IsSurjective )
open import Base.Equality   using ( swelldef )
open import Base.Relations  using ( ker ; ker-IsEquivalence ; ⟪_⟫ ; mkblk )

open  import Base.Algebras {𝑆 = 𝑆}
      using ( Algebra ; compatible ; _̂_ ; Con ; mkcon ; _╱_ ; IsCongruence ; /-≡ )

open import Base.Homomorphisms.Basic {𝑆 = 𝑆}  using ( hom ; epi ; epi→hom )

private variable α β : Level

module _ {𝑨 : Algebra α} where
 open ≡-Reasoning
 homker-comp :  swelldef 𝓥 β → {𝑩 : Algebra β}(h : hom 𝑨 𝑩)
  →             compatible 𝑨 (ker ∣ h ∣)

 homker-comp wd {𝑩} h f {u}{v} kuv =
  ∣ h ∣((f ̂ 𝑨) u)    ≡⟨ ∥ h ∥ f u ⟩
  (f ̂ 𝑩)(∣ h ∣ ∘ u)  ≡⟨ wd(f ̂ 𝑩)(∣ h ∣ ∘ u)(∣ h ∣ ∘ v)kuv ⟩
  (f ̂ 𝑩)(∣ h ∣ ∘ v)  ≡⟨ (∥ h ∥ f v)⁻¹ ⟩
  ∣ h ∣((f ̂ 𝑨) v)    ∎

 kercon : swelldef 𝓥 β → {𝑩 : Algebra β} → hom 𝑨 𝑩 → Con{α}{β} 𝑨
 kercon wd {𝑩} h = ker ∣ h ∣ , mkcon (ker-IsEquivalence ∣ h ∣)(homker-comp wd {𝑩} h)

 kerquo : swelldef 𝓥 β → {𝑩 : Algebra β} → hom 𝑨 𝑩 → Algebra (α ⊔ suc β)
 kerquo wd {𝑩} h = 𝑨 ╱ (kercon wd {𝑩} h)

ker[_⇒_]_↾_ :  (𝑨 : Algebra α)(𝑩 : Algebra β) → hom 𝑨 𝑩 → swelldef 𝓥 β
 →             Algebra (α ⊔ suc β)

ker[ 𝑨 ⇒ 𝑩 ] h ↾ wd = kerquo wd {𝑩} h

module _ {α β : Level}{𝑨 : Algebra α} where
 πepi : (θ : Con{α}{β} 𝑨) → epi 𝑨 (𝑨 ╱ θ)
 πepi θ = (λ a → ⟪ a ⟫) , (λ _ _ → refl) , cπ-is-epic  where
  cπ-is-epic : IsSurjective (λ a → ⟪ a ⟫)
  cπ-is-epic (C , mkblk a refl ) =  Image_∋_.eq a refl

 πhom : (θ : Con{α}{β} 𝑨) → hom 𝑨 (𝑨 ╱ θ)
 πhom θ = epi→hom (𝑨 ╱ θ) (πepi θ)

 πker :  (wd : swelldef 𝓥 β){𝑩 : Algebra β}(h : hom 𝑨 𝑩)
  →      epi 𝑨 (ker[ 𝑨 ⇒ 𝑩 ] h ↾ wd)

 πker wd {𝑩} h = πepi (kercon wd {𝑩} h)

 open IsCongruence

 ker-in-con :  {wd : swelldef 𝓥 (α ⊔ suc β)}(θ : Con 𝑨)
  →            ∀ {x}{y} → ∣ kercon wd {𝑨 ╱ θ} (πhom θ) ∣ x y →  ∣ θ ∣ x y

 ker-in-con θ hyp = /-≡ θ hyp

