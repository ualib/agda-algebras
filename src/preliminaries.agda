module Preliminaries where

-- Export common imports
open import Level public
open import Data.Product using (∃; _,_) public renaming (proj₁ to ∣_∣; proj₂ to ⟦_⟧)
open import Relation.Unary using (Pred; _∈_; _⊆_) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl) public
open import Function using (_∘_) public

_∈∈_ : {i j k : Level} {A : Set i} {B : Set j} → (A → B) → Pred B k → Set (i ⊔ k)
_∈∈_ {A = A} f S = (x : A) → f x ∈ S
