
{-# OPTIONS --without-K --exact-split --safe #-}

module Examples.Structures.Signatures where

open import Agda.Primitive         using () renaming ( lzero to ℓ₀ )
open import Data.Unit.Base         using () renaming ( ⊤ to 𝟙 ; tt to 𝟎 )
open import Data.Empty             using () renaming ( ⊥ to 𝟘 )
open import Overture               using ( 𝟚 ; 𝟛 )
open import Base.Structures.Basic  using ( signature ; structure )

S∅ : signature ℓ₀ ℓ₀
S∅ = record { symbol = 𝟘 ; arity = λ () }

S1 : signature ℓ₀ ℓ₀
S1 = record { symbol = 𝟙 ; arity = λ _ → 𝟘 }

S01 : signature ℓ₀ ℓ₀ -- ...one unary
S01 = record { symbol = 𝟙 ; arity = λ _ → 𝟙 }

S001 : signature ℓ₀ ℓ₀
S001 = record { symbol = 𝟙 ; arity = λ _ → 𝟚 }

S0001 : signature ℓ₀ ℓ₀
S0001 = record { symbol = 𝟙 ; arity = λ _ → 𝟛 }

S021 : signature ℓ₀ ℓ₀
S021 = record { symbol = 𝟛 ; arity = λ{ 𝟛.𝟎 → 𝟚 ; 𝟛.𝟏 → 𝟙 ; 𝟛.𝟐 → 𝟙 } }

S101 : signature ℓ₀ ℓ₀
S101 = record { symbol = 𝟚 ; arity = λ{ 𝟚.𝟎 → 𝟘 ; 𝟚.𝟏 → 𝟚 } }

S111 : signature ℓ₀ ℓ₀
S111 = record { symbol = 𝟛 ; arity = λ{ 𝟛.𝟎 → 𝟘 ; 𝟛.𝟏 → 𝟙 ; 𝟛.𝟐 → 𝟚 } }

