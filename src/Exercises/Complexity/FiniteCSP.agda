
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Exercises.Complexity.FiniteCSP  where

open import Agda.Primitive  using ( ) renaming (lzero to ℓ₀ )
open import Data.Product    using ( _,_ ; _×_ )
open import Data.Unit.Base  using () renaming ( tt to 𝟎 )
open import Relation.Unary  using ( Pred ; _∈_ )

open import Overture.Basic                  using ( 𝟚 ; 𝟛 )
open import Base.Relations.Continuous       using ( Rel )
open import Base.Structures.Basic           using ( signature ; structure )
open import Examples.Structures.Signatures  using ( S∅ ; S001 ; S021)
open import Base.Structures.Homs            using ( hom )
open signature
open structure

module solution-2-1 where

 data Rᵃ : Pred (𝟚 × 𝟚) ℓ₀ where
  r1 : (𝟚.𝟎 , 𝟚.𝟎 ) ∈ Rᵃ
  r2 : (𝟚.𝟏 , 𝟚.𝟏 ) ∈ Rᵃ

 𝑨 : structure S∅    -- (no operation symbols)
               S001  -- (one binary relation symbol)

 𝑨 = record { carrier = 𝟚
            ; op = λ ()
            ; rel = λ _ x → ((x 𝟚.𝟎) , (x 𝟚.𝟏)) ∈ Rᵃ
            }

 claim : (𝑩 : structure {ℓ₀}{ℓ₀}{ℓ₀}{ℓ₀} S∅ S001 {ℓ₀}{ℓ₀}) → hom 𝑩 𝑨
 claim 𝑩 = (λ x → 𝟚.𝟎) , (λ _ _ _ → r1) , λ ()

module solution-2-2 where

 data Rᵃ : Pred (𝟚 × 𝟚) ℓ₀ where
  r1 : (𝟚.𝟎 , 𝟚.𝟎 ) ∈ Rᵃ
  r2 : (𝟚.𝟏 , 𝟚.𝟏 ) ∈ Rᵃ

 data C₀ᵃ : Pred 𝟚 ℓ₀ where
  c₀ : 𝟚.𝟎 ∈ C₀ᵃ

 data C₁ᵃ : Pred 𝟚 ℓ₀ where
  c₁ : 𝟚.𝟏 ∈ C₁ᵃ

 𝑨 : structure S∅    -- (no operations)
               S021  -- (two unary relations and one binary relation)

 𝑨 = record { carrier = 𝟚
            ; op = λ ()
            ; rel = rels
            }
            where
            rels : (r : 𝟛) → Rel 𝟚 (arity S021 r)
            rels 𝟛.𝟎 x = ((x 𝟚.𝟎) , (x 𝟚.𝟏)) ∈ Rᵃ
            rels 𝟛.𝟏 x = x 𝟎 ∈ C₀ᵃ
            rels 𝟛.𝟐 x = x 𝟎 ∈ C₁ᵃ

