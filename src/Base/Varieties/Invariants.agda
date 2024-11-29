
{-# OPTIONS --without-K --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Base.Varieties.Invariants (𝑆 : Signature 𝓞 𝓥) where

open import Agda.Primitive  using () renaming ( Set to Type )
open import Level           using ( Level )
open import Relation.Unary  using ( Pred )

open import Base.Homomorphisms   {𝑆 = 𝑆} using ( _≅_ )
open import Base.Algebras.Basic  {𝑆 = 𝑆} using ( Algebra )

private variable α ℓ : Level

AlgebraicInvariant : Pred (Algebra α) ℓ → Type _
AlgebraicInvariant P = ∀ 𝑨 𝑩 → P 𝑨 → 𝑨 ≅ 𝑩 → P 𝑩

