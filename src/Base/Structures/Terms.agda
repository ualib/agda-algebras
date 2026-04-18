
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Base.Structures.Terms where

open import Agda.Primitive  using () renaming ( Set to Type )
open import Level           using ( Level )

open import Base.Structures.Basic  using ( signature ; structure ; _ᵒ_ )
open import Base.Terms.Basic

private variable
 𝓞₀ 𝓥₀ 𝓞₁ 𝓥₁ χ α ρ : Level
 𝐹 : signature 𝓞₀ 𝓥₀
 𝑅 : signature 𝓞₁ 𝓥₁
 X : Type χ

open signature
open structure

_⟦_⟧ : (𝑨 : structure 𝐹 𝑅 {α} {ρ}) → Term X → (X → carrier 𝑨) → carrier 𝑨
𝑨 ⟦ ℊ x ⟧ = λ a → a x
𝑨 ⟦ node f t ⟧ = λ a → (f ᵒ 𝑨) (λ i → (𝑨 ⟦ t i ⟧ ) a)

