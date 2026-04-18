
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Base.Adjunction.Galois where

open import Agda.Primitive           using () renaming ( Set to Type )
open import Data.Product             using ( _,_ ; _×_ ; swap ) renaming ( proj₁ to fst )
open import Function.Base            using ( _∘_ ; id )
open import Level                    using ( _⊔_ ;  Level ; suc )
open import Relation.Binary.Bundles  using ( Poset )
open import Relation.Binary.Core     using ( REL ; Rel ; _⇒_ ; _Preserves_⟶_ )
open import Relation.Unary           using ( _⊆_ ;  _∈_ ; Pred   )

import Relation.Binary.Structures as BS

private variable α β ℓᵃ ρᵃ ℓᵇ ρᵇ : Level

module _ (A : Poset α ℓᵃ ρᵃ)(B : Poset β ℓᵇ ρᵇ) where
 open Poset
 private
  _≤A_ = _≤_ A
  _≤B_ = _≤_ B

 record Galois : Type (suc (α ⊔ β ⊔ ρᵃ ⊔ ρᵇ))  where
  field
   F : Carrier A → Carrier B
   G : Carrier B → Carrier A
   GF≥id : ∀ a →  a ≤A G (F a)
   FG≥id : ∀ b →  b ≤B F (G b)

module _ {𝒜 : Type α}{ℬ : Type β} where

 _⃗_ : ∀ {ρᵃ ρᵇ} → Pred 𝒜 ρᵃ → REL 𝒜 ℬ ρᵇ → Pred ℬ (α ⊔ ρᵃ ⊔ ρᵇ)
 A ⃗ R = λ b → A ⊆ (λ a → R a b)

 _⃖_ : ∀ {ρᵃ ρᵇ} → REL 𝒜 ℬ ρᵃ → Pred ℬ ρᵇ → Pred 𝒜 (β ⊔ ρᵃ ⊔ ρᵇ)
 R ⃖ B = λ a → B ⊆ R a

 ←→≥id : ∀ {ρᵃ ρʳ} {A : Pred 𝒜 ρᵃ} {R : REL 𝒜 ℬ ρʳ} → A ⊆ R ⃖ (A ⃗ R)
 ←→≥id p b = b p

 →←≥id : ∀ {ρᵇ ρʳ} {B : Pred ℬ ρᵇ} {R : REL 𝒜 ℬ ρʳ}  → B ⊆ (R ⃖ B) ⃗ R
 →←≥id p a = a p

 →←→⊆→ : ∀ {ρᵃ ρʳ} {A : Pred 𝒜 ρᵃ}{R : REL 𝒜 ℬ ρʳ} → (R ⃖ (A ⃗ R)) ⃗ R ⊆ A ⃗ R
 →←→⊆→ p a = p (λ z → z a)

 ←→←⊆← : ∀ {ρᵇ ρʳ} {B : Pred ℬ ρᵇ}{R : REL 𝒜 ℬ ρʳ}  → R ⃖ ((R ⃖ B) ⃗ R) ⊆ R ⃖ B
 ←→←⊆← p b = p (λ z → z b)

 ←→Closed : ∀ {ρᵃ ρʳ} {A : Pred 𝒜 ρᵃ} {R : REL 𝒜 ℬ ρʳ} → Type _
 ←→Closed {A = A}{R} = R ⃖ (A ⃗ R) ⊆ A

 →←Closed : ∀ {ρᵇ ρʳ} {B : Pred ℬ ρᵇ}{R : REL 𝒜 ℬ ρʳ} → Type _
 →←Closed {B = B}{R} = (R ⃖ B) ⃗ R ⊆ B

open Poset

module _ {α ρ : Level} {𝒜 : Type α} where

 _≐_ : Pred 𝒜 ρ → Pred 𝒜 ρ → Type (α ⊔ ρ)
 P ≐ Q = (P ⊆ Q) × (Q ⊆ P)

 open BS.IsEquivalence renaming (refl to ref ; sym to symm ; trans to tran)

 ≐-iseqv : BS.IsEquivalence _≐_
 ref ≐-iseqv = id , id
 symm ≐-iseqv = swap
 tran ≐-iseqv (u₁ , u₂) (v₁ , v₂) = v₁ ∘ u₁ , u₂ ∘ v₂

module _ {α : Level} (ρ : Level) (𝒜 : Type α) where

 PosetOfSubsets : Poset (α ⊔ suc ρ) (α ⊔ ρ) (α ⊔ ρ)
 Carrier PosetOfSubsets = Pred 𝒜 ρ
 _≈_ PosetOfSubsets = _≐_
 _≤_ PosetOfSubsets = _⊆_
 isPartialOrder PosetOfSubsets =
  record  { isPreorder = record  { isEquivalence = ≐-iseqv
                                 ; reflexive = fst
                                 ; trans = λ u v → v ∘ u
                                 }
          ; antisym = _,_
          }

module _ {ℓ : Level}{𝒜 : Type ℓ} {ℬ : Type ℓ} where

 𝒫𝒜 : Poset (suc ℓ) ℓ ℓ
 𝒫ℬ : Poset (suc ℓ) ℓ ℓ
 𝒫𝒜 = PosetOfSubsets ℓ 𝒜
 𝒫ℬ = PosetOfSubsets ℓ ℬ

 Rel→Gal : (R : REL 𝒜 ℬ ℓ) → Galois 𝒫𝒜 𝒫ℬ
 Rel→Gal R = record  { F = _⃗ R
                     ; G = R ⃖_
                     ; GF≥id = λ _ → ←→≥id
                     ; FG≥id = λ _ → →←≥id }

