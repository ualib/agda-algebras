
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Overture.Signatures where

open import Agda.Primitive  using () renaming ( Set to  Type )
open import Data.Product    using ( Σ-syntax )
open import Level           using ( Level ; suc ; _⊔_ )

variable 𝓞 𝓥 : Level

Signature : (𝓞 𝓥 : Level) → Type (suc (𝓞 ⊔ 𝓥))
Signature 𝓞 𝓥 = Σ[ F ∈ Type 𝓞 ] (F → Type 𝓥)

Level-of-Signature : {𝓞 𝓥 : Level} → Signature 𝓞 𝓥 → Level
Level-of-Signature {𝓞}{𝓥} _ = suc (𝓞 ⊔ 𝓥)

