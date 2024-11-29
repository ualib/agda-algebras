
{-# OPTIONS --without-K --exact-split --safe #-}

module Base.Adjunction.Residuation where

open import Agda.Primitive           using () renaming ( Set to Type )
open import Function.Base            using ( _on_ ; _∘_ )
open import Level                    using ( Level ; _⊔_ ; suc )
open import Relation.Binary.Bundles  using ( Poset )
open import Relation.Binary.Core     using ( _Preserves_⟶_ )

open import Base.Relations.Discrete using ( PointWise )

private variable
 a ιᵃ α b ιᵇ β : Level

module _ (A : Poset a ιᵃ α)(B : Poset b ιᵇ β) where
 open Poset
 private
  _≤A_ = _≤_ A
  _≤B_ = _≤_ B

 record Residuation : Type (suc (α ⊔ a ⊔ β ⊔ b))  where
  field
   f      : Carrier A → Carrier B
   g      : Carrier B → Carrier A
   fhom   : f Preserves _≤A_ ⟶ _≤B_
   ghom   : g Preserves _≤B_ ⟶ _≤A_
   gf≥id  : ∀ a → a ≤A g (f a)
   fg≤id  : ∀ b → f (g b) ≤B b

open Residuation
open Poset

module _ {A : Poset a ιᵃ α} {B : Poset b ιᵇ β} (R : Residuation A B) where
 private
  _≤A_ = _≤_ A
  _≤B_ = _≤_ B

  𝑓 = (R .f)
  𝑔 = (R .g)

  _≈̇A_ = PointWise{a = b}{A = Carrier B} (_≈_ A)
  _≈̇B_ = PointWise{a = a}{A = Carrier A} (_≈_ B)

 weak-inverse : (𝑓 ∘ 𝑔 ∘ 𝑓) ≈̇B 𝑓
 weak-inverse a = antisym B lt gt
  where
  lt : 𝑓 (𝑔 (𝑓 a)) ≤B 𝑓 a
  lt = fg≤id R (𝑓 a)
  gt : 𝑓 a ≤B 𝑓 (𝑔 (𝑓 a))
  gt = fhom R (gf≥id R a)

 weak-inverse' : (𝑔 ∘ 𝑓 ∘ 𝑔) ≈̇A 𝑔
 weak-inverse' b = antisym A lt gt
  where
  lt : 𝑔 (𝑓 (𝑔 b)) ≤A 𝑔 b
  lt = ghom R (fg≤id R b)
  gt : 𝑔 b ≤A 𝑔 (𝑓 (𝑔 b))
  gt = gf≥id R (𝑔 b)

