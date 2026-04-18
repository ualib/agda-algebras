
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Base.Structures.Products where

open import Agda.Primitive  using () renaming ( Set to Type )
open import Data.Product    using ( _,_ ; Σ-syntax )
open import Level           using ( Level ; suc ; _⊔_ )
open import Relation.Unary  using ( _∈_ ; Pred )

open import Overture               using ( ∣_∣ ; Π-syntax )
open import Base.Structures.Basic  using ( signature ; structure )

private variable
 𝓞₀ 𝓥₀ 𝓞₁ 𝓥₁ : Level
 𝐹 : signature 𝓞₀ 𝓥₀
 𝑅 : signature 𝓞₁ 𝓥₁
 α ρ ℓ : Level

open structure

⨅ : {ℑ : Type ℓ}(𝒜 : ℑ → structure 𝐹 𝑅 {α}{ρ} ) → structure 𝐹 𝑅
⨅ {ℑ = ℑ} 𝒜 =
 record  { carrier = Π[ i ∈ ℑ ] carrier (𝒜 i)             -- domain of the product structure
         ; op = λ 𝑓 a i → (op (𝒜 i) 𝑓) λ x → a x i        -- interpretation of  operations
         ; rel = λ r a → ∀ i → (rel (𝒜 i) r) λ x → a x i  -- interpretation of relations
         }

module _ {𝒦 : Pred (structure 𝐹 𝑅 {α}{ρ}) ℓ} where
  ℓp : Level
  ℓp = suc (α ⊔ ρ) ⊔ ℓ

  ℑ : Type _
  ℑ = Σ[ 𝑨 ∈ structure 𝐹 𝑅  {α}{ρ}] 𝑨 ∈ 𝒦

  𝔄 : ℑ → structure 𝐹 𝑅 {α}{ρ}
  𝔄 𝔦 = ∣ 𝔦 ∣

  class-product : structure 𝐹 𝑅
  class-product = ⨅ 𝔄

