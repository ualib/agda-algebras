
{-# OPTIONS --without-K --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Base.Complexity.CSP {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive   using ( _⊔_ ; lsuc ; Level) renaming ( Set to Type )
open import Function.Base    using ( _∘_ )
open import Relation.Binary  using ( Setoid )

open import Base.Relations.Continuous       using ( REL ; REL-syntax )
open import Setoid.Algebras.Basic  {𝑆 = 𝑆}  using ( Algebra )

module  _              -- levels for...
        {ι : Level}    -- ...arity (or argument index) types
        {ν : Level}    -- ...variable symbol types
        {α ℓ : Level}  -- ... domain types
 where
 open Setoid
 record Constraint (var : Type ν) (dom : var → Setoid α ℓ) : Type (ν ⊔ α ⊔ lsuc ι) where
  field
   arity  : Type ι               -- The "number" of variables involved in the constraint.
   scope  : arity → var          -- Which variables are involved in the constraint.
   rel    : REL[ i ∈ arity ] (Carrier (dom (scope i)))   -- The constraint relation.

  satisfies : (∀ v → Carrier (dom v)) → Type  -- An assignment 𝑓 : var → dom of values to variables
  satisfies f = rel (f ∘ scope)      -- *satisfies* the constraint 𝐶 = (σ , 𝑅) provided

 open Algebra
 open Setoid
 record CSPInstance (var : Type ν)(𝒜 : var → Algebra α ℓ) : Type (ν ⊔ α ⊔ lsuc ι) where
  field
   ar : Type ι       -- ar indexes the contraints in the instance
   cs : (i : ar) → Constraint var (λ v → Domain (𝒜 v))

  isSolution : (∀ v → Carrier (Domain (𝒜 v))) → Type _  -- An assignment *solves* the instance
  isSolution f = ∀ i → (Constraint.satisfies (cs i)) f  -- if it satisfies all the constraints.

