
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Relation.Binary using ( Setoid )

module Setoid.Functions.Bijective {α ρᵃ β ρᵇ}{𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where

open import Agda.Primitive    using ( _⊔_ ; Level )  renaming ( Set to Type )
open import Data.Product      using ( _,_ ; _×_ )
open import Function.Bundles  using ()               renaming ( Func to _⟶_ )

open import Setoid.Functions.Inverses    using ( Image_∋_ ; Inv )
open import Setoid.Functions.Surjective  using ( IsSurjective )
open import Setoid.Functions.Injective   using ( IsInjective )

open Image_∋_

open Setoid 𝑨  using ()               renaming (Carrier to A; _≈_ to _≈₁_)
open Setoid 𝑩  using ( sym ; trans )  renaming (Carrier to B; _≈_ to _≈₂_)

IsBijective : (𝑨 ⟶ 𝑩) → Type (α ⊔ β ⊔ ρᵃ ⊔ ρᵇ)
IsBijective f = IsInjective f × IsSurjective f

BijInv : (f : 𝑨 ⟶ 𝑩) → IsBijective f → 𝑩 ⟶ 𝑨
BijInv f (fM , fE) = record { to = finv ; cong = c }
 where
 finv : B → A
 finv b = Inv f fE

 handler :  ∀ {b₀ b₁}(i₀ : Image f ∋ b₀)(i₁ : Image f ∋ b₁)
  →         b₀ ≈₂ b₁ → (Inv f i₀) ≈₁ (Inv f i₁)

 handler (eq a x) (eq a₁ x₁) b₀≈b₁ = fM (trans (sym x) (trans b₀≈b₁ x₁))

 c : ∀ {b₀ b₁} → b₀ ≈₂ b₁ → (finv b₀) ≈₁ (finv b₁)
 c b₀≈b₁ = handler fE fE b₀≈b₁

