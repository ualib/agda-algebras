{-# OPTIONS --without-K --exact-split #-}

open import Level
open import Data.Product using (∃; _,_) renaming (proj₁ to ∣_∣)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (_∘_)

module NewBasic where

-- Operations and projections
module _ {i j} where
  Op : Set i → Set j → Set (i ⊔ j)
  Op I A = (I → A) → A

  π : {I : Set i} {A : Set j} → I → Op I A
  π i x = x i

-- i is the universe in which the carrier lives
-- j is the universe in which the arities live
Signature : (i j : Level) → Set (suc (i ⊔ j))
Signature i j = ∃ λ (F : Set i) → F → Set j

private
  variable
    i j : Level

-- k is the universe in which the operational type lives
Algebra : (k : Level) → Signature i j → Set (i ⊔ j ⊔ suc k)
Algebra k (F , ρ) = ∃ λ (A : Set k) → (o : F) → Op (ρ o) A

private
  variable
    k : Level
    S : Signature i j

-- The category of homomorphisms Hom(A, B) = (id, _>>>_)
Hom : Algebra k S → Algebra k S → Set _
Hom {S = F , ρ} (a , A) (b , B) =
  ∃ λ (f : a → b) → (o : F) (x : ρ o → a) → f (A o x) ≡ B o (f ∘ x)

id : (A : Algebra k S) → Hom A A
id (a , A) = (λ x → x) , λ _ _ → refl

private
  variable
    A B : Algebra k S

_>>>_ : {C : Algebra k S} → Hom A B → Hom B C → Hom A C
_>>>_ {S = F , ρ} {A = a , A} {C = c , C} (f , α) (g , β) = g ∘ f , γ where
  γ : (o : F) (x : ρ o → a) → (g ∘ f) (A o x) ≡ C o (g ∘ f ∘ x)
  γ o x rewrite α o x = β o (f ∘ x)

-- Equalizers in Hom
_~_ : Hom A B → Hom A B → ∣ A ∣ → Set _
_~_ (f , _) (g , _) x = f x ≡ g x

