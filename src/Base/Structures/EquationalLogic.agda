
{-# OPTIONS --without-K --exact-split --safe #-}

module Base.Structures.EquationalLogic where

open import Agda.Primitive  using () renaming ( Set to Type )
open import Data.Fin.Base   using ( Fin )
open import Data.Nat        using ( ℕ )
open import Data.Product    using ( _×_ ; _,_ ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Level           using ( Level )
open import Relation.Unary  using ( Pred ; _∈_ )

open import Overture               using ( _≈_ )
open import Base.Terms             using ( Term )
open import Base.Structures.Basic  using ( signature ; structure ; _ᵒ_ )
open import Base.Structures.Terms  using ( _⟦_⟧ )

private variable
 𝓞₀ 𝓥₀ 𝓞₁ 𝓥₁ χ α ρ ℓ : Level
 𝐹 : signature 𝓞₀ 𝓥₀
 𝑅 : signature 𝓞₁ 𝓥₁
 X : Type χ

_⊧_≈_ : structure 𝐹 𝑅 {α}{ρ} → Term X → Term X → Type _
𝑨 ⊧ p ≈ q = 𝑨 ⟦ p ⟧ ≈ 𝑨 ⟦ q ⟧

_⊧_≋_ : Pred(structure 𝐹 𝑅 {α}{ρ}) ℓ → Term X → Term X → Type _
𝒦 ⊧ p ≋ q = ∀{𝑨 : structure _ _} → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q

Th : Pred (structure 𝐹 𝑅{α}{ρ}) ℓ → Pred(Term X × Term X) _ -- (ℓ₁ ⊔ χ)
Th 𝒦 = λ (p , q) → 𝒦 ⊧ p ≋ q

Mod : Pred(Term X × Term X) ℓ  → Pred(structure 𝐹 𝑅 {α} {ρ}) _  -- (χ ⊔ ℓ₀)
Mod ℰ = λ 𝑨 → ∀ p q → (p , q) ∈ ℰ → 𝑨 ⊧ p ≈ q

fMod : {n : ℕ} → (Fin n → (Term X × Term X)) → Pred(structure 𝐹 𝑅 {α} {ρ}) _
fMod ℰ = λ 𝑨 → ∀ i → 𝑨 ⊧ fst (ℰ i) ≈ snd (ℰ i)

