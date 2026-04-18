
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Base.Structures.Sigma.Products where

open import Agda.Primitive  using ( _⊔_ ; lsuc ) renaming ( Set to Type )
open import Data.Product    using ( _,_ ; _×_ ; Σ-syntax )
open import Level           using ( Level ; Lift )
open import Relation.Unary  using ( _∈_ ; Pred )

open import Overture                     using ( ∣_∣ ; ∥_∥ ; Π ; Π-syntax )
open import Base.Structures.Sigma.Basic  using ( Signature ; Structure ; _ʳ_ ; _ᵒ_ )

private variable
 𝑅 𝐹 : Signature
 α ρ ι : Level

⨅ : {ℑ : Type ι}(𝒜 : ℑ → Structure  𝑅 𝐹{α}{ρ}) → Structure 𝑅 𝐹 {α ⊔ ι} {ρ ⊔ ι}
⨅ {ℑ = ℑ} 𝒜 =  Π[ 𝔦 ∈ ℑ ] ∣ 𝒜 𝔦 ∣                         -- domain of the product structure
               , ( λ r a → ∀ 𝔦 → (r ʳ 𝒜 𝔦) λ x → a x 𝔦 )  -- interpretations of relations
               , ( λ 𝑓 a 𝔦 → (𝑓 ᵒ 𝒜 𝔦) λ x → a x 𝔦 )      -- interpretations of  operations

module _ {α ρ τ : Level}{𝒦 : Pred (Structure 𝑅 𝐹 {α}{ρ}) τ} where

 ℓp : Level
 ℓp = lsuc (α ⊔ ρ) ⊔ τ

 ℑ : Type ℓp
 ℑ = Σ[ 𝑨 ∈ Structure 𝑅 𝐹 ] (𝑨 ∈ 𝒦)

 𝔖 : ℑ → Structure 𝑅 𝐹        -- (type \MfS to get 𝔖)
 𝔖 𝔦 = ∣ 𝔦 ∣

 class-prod : Structure 𝑅 𝐹
 class-prod = ⨅ 𝔖

