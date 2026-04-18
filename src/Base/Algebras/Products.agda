
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Base.Algebras.Products {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive  using () renaming ( Set to Type )
open import Data.Product    using ( _,_ ; Σ ; Σ-syntax )
open import Level           using ( Level ; _⊔_ ; suc )
open import Relation.Unary  using ( Pred ; _⊆_ ; _∈_ )

open import Overture                     using (_⁻¹; 𝑖𝑑; ∣_∣; ∥_∥)
open import Base.Algebras.Basic {𝑆 = 𝑆}  using ( Algebra ; _̂_ ; algebra )

private variable α β ρ 𝓘 : Level

⨅ : {I : Type 𝓘 }(𝒜 : I → Algebra α ) → Algebra (𝓘 ⊔ α)

⨅ {I = I} 𝒜 =  ( ∀ (i : I) → ∣ 𝒜 i ∣ ) ,        -- domain of the product algebra
                λ 𝑓 𝑎 i → (𝑓 ̂ 𝒜 i) λ x → 𝑎 x i  -- basic operations of the product algebra

open algebra

⨅' : {I : Type 𝓘 }(𝒜 : I → algebra α) → algebra (𝓘 ⊔ α)
⨅' {I} 𝒜 = record  { carrier = ∀ i → carrier (𝒜 i)                         -- domain
                    ; opsymbol = λ 𝑓 𝑎 i → (opsymbol (𝒜 i)) 𝑓 λ x → 𝑎 x i }  -- basic operations

ov : Level → Level
ov α = 𝓞 ⊔ 𝓥 ⊔ suc α

module _ {𝒦 : Pred (Algebra α)(ov α)} where
 ℑ : Type (ov α)
 ℑ = Σ[ 𝑨 ∈ Algebra α ] 𝑨 ∈ 𝒦

 𝔄 : ℑ → Algebra α
 𝔄 i = ∣ i ∣

 class-product : Algebra (ov α)
 class-product = ⨅ 𝔄

