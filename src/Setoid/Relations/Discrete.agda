
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Relations.Discrete where

open import Agda.Primitive        using () renaming ( Set to Type )
open import Data.Product          using ( _,_ ; _×_ )
open import Function              using ( _∘_ ) renaming ( Func to _⟶_ )
open import Level                 using ( Level ;  _⊔_ ; Lift )
open import Relation.Binary       using ( IsEquivalence ; Setoid )
open import Relation.Binary.Core  using ( _⇒_ ; _=[_]⇒_ )
                                  renaming ( REL to BinREL ; Rel to BinRel )
open import Relation.Binary.Definitions
                                  using ( Reflexive ; Transitive )
open import Relation.Unary        using ( _∈_; Pred )
open import Relation.Binary.PropositionalEquality
                                  using ( _≡_ )

open import Overture using ( Π-syntax )

private variable α β ρᵃ ρᵇ ℓ 𝓥 : Level

open _⟶_ renaming ( to to _⟨$⟩_ )
module _ {𝐴 : Setoid α ρᵃ}{𝐵 : Setoid β ρᵇ} where
 open Setoid 𝐴  using () renaming ( Carrier to A ; _≈_ to _≈₁_ )
 open Setoid 𝐵  using () renaming ( Carrier to B ; _≈_ to _≈₂_ )

 function-equality : BinRel (𝐴 ⟶ 𝐵) (α ⊔ ρᵇ)
 function-equality f g = ∀ x → f ⟨$⟩ x ≈₂ g ⟨$⟩ x

 Im_⊆_ : (𝐴 ⟶ 𝐵) → Pred B ℓ → Type (α ⊔ ℓ)
 Im f ⊆ S = ∀ x → f ⟨$⟩ x ∈ S

 fker : (𝐴 ⟶ 𝐵) → BinRel A ρᵇ
 fker g x y = g ⟨$⟩ x ≈₂ g ⟨$⟩ y

 fkerPred : (𝐴 ⟶ 𝐵) → Pred (A × A) ρᵇ
 fkerPred g (x , y) = g ⟨$⟩ x ≈₂ g ⟨$⟩ y

 open IsEquivalence

 fkerlift : (𝐴 ⟶ 𝐵) → (ℓ : Level) → BinRel A (ℓ ⊔ ρᵇ)
 fkerlift g ℓ x y = Lift ℓ (g ⟨$⟩ x ≈₂ g ⟨$⟩ y)

 0rel : {ℓ : Level} → BinRel A (ρᵃ ⊔ ℓ)
 0rel {ℓ} = λ x y → Lift ℓ (x ≈₁ y)

