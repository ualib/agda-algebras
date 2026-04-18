
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Base.Adjunction.Closure where

open import Agda.Primitive           using () renaming ( Set to Type )
import Algebra.Definitions
open import Data.Product             using ( Σ-syntax ; _,_ ; _×_ )
open import Function                 using ( _∘₂_ )
open import Function.Bundles         using ( _↔_ ; Inverse)
open import Level                    using ( _⊔_ ; Level )
open import Relation.Binary.Bundles  using ( Poset )
open import Relation.Binary.Core     using ( Rel ; _Preserves_⟶_ )
open import Relation.Unary           using ( Pred ; _∈_ ; ⋂ )

import Relation.Binary.Reasoning.PartialOrder as ≤-Reasoning

private variable
 α ρ ℓ ℓ₁ ℓ₂ : Level
 a : Type α

Extensive : Rel a ρ → (a → a) → Type _
Extensive _≤_ C = ∀{x} → x ≤ C x

module _ {χ ρ ℓ : Level}{X : Type χ} where

 IntersectClosed : Pred (Pred X ℓ) ρ → Type _
 IntersectClosed C = ∀ {I : Type ℓ}{c : I → Pred X ℓ} → (∀ i → (c i) ∈ C) → ⋂ I c ∈ C

 ClosureSystem : Type _
 ClosureSystem = Σ[ C ∈ Pred (Pred X ℓ) ρ ] IntersectClosed C

record ClOp {ℓ ℓ₁ ℓ₂ : Level}(𝑨 : Poset ℓ ℓ₁ ℓ₂) : Type  (ℓ ⊔ ℓ₂ ⊔ ℓ₁) where
 open Poset 𝑨
 private A = Carrier
 open Algebra.Definitions (_≈_)
 field
  C : A → A
  isExtensive        : Extensive _≤_ C
  isOrderPreserving  : C Preserves _≤_ ⟶ _≤_
  isIdempotent       : IdempotentFun C

open ClOp
open Inverse

module _ {𝑨 : Poset ℓ ℓ₁ ℓ₂}(𝑪 : ClOp 𝑨) where
 open Poset 𝑨
 open ≤-Reasoning 𝑨
 private
  c = C 𝑪
  A = Carrier

 clop→law⇒ : (x y : A) → x ≤ (c y) → (c x) ≤ (c y)
 clop→law⇒ x y x≤cy = begin
   c x      ≤⟨ isOrderPreserving 𝑪 x≤cy ⟩
   c (c y)  ≈⟨ isIdempotent 𝑪 y ⟩
   c y      ∎

 clop→law⇐ : (x y : A) → (c x) ≤ (c y) → x ≤ (c y)
 clop→law⇐ x y cx≤cy = begin
   x    ≤⟨ isExtensive 𝑪 ⟩
   c x  ≤⟨ cx≤cy ⟩
   c y  ∎

module _ {𝑨 : Poset ℓ ℓ₁ ℓ₂} where
 open Poset 𝑨
 private A = Carrier
 open Algebra.Definitions (_≈_)

 clop←law :  (c : A → A) → ((x y : A) → (x ≤ (c y) ↔ (c x) ≤ (c y)))
  →          Extensive _≤_ c × c Preserves _≤_ ⟶ _≤_ × IdempotentFun c

 clop←law c hyp  = e , (o , i)
  where
  e : Extensive _≤_ c
  e = (from ∘₂ hyp) _ _ refl

  o : c Preserves _≤_ ⟶ _≤_
  o u = (to ∘₂ hyp) _ _ (trans u e)

  i : IdempotentFun c
  i x = antisym ((to ∘₂ hyp) _ _ refl) ((from ∘₂ hyp) _ _ refl)

