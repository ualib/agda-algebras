
{-# OPTIONS --without-K --exact-split --safe #-}

module Overture.Basic where

open import Agda.Primitive    using () renaming ( Set to  Type ; lzero to  ℓ₀ )
open import Data.Product      using ( _,_ ; ∃ ; Σ-syntax ; _×_ )
                              renaming ( proj₁ to fst ; proj₂ to snd )
open import Function.Base     using ( _∘_ ; id )
open import Level             using ( Level ; suc ; _⊔_ ; lift ; lower ; Lift )
open import Relation.Binary   using ( Decidable )
open import Relation.Binary   using ( IsEquivalence ; IsPartialOrder )
open import Relation.Nullary  using ( Dec ; yes ; no ; Irrelevant )

open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; trans )

private variable a b : Level

ℓ₁ : Level
ℓ₁ = suc ℓ₀

data 𝟚 : Type ℓ₀ where 𝟎 : 𝟚 ;  𝟏 : 𝟚

data 𝟛 : Type ℓ₀ where 𝟎 : 𝟛 ;  𝟏 : 𝟛 ;  𝟐 : 𝟛

module _ {A : Type a}{B : A → Type b} where

 ∣_∣ : Σ[ x ∈ A ] B x → A
 ∣_∣ = fst

 ∥_∥ : (z : Σ[ a ∈ A ] B a) → B ∣ z ∣
 ∥_∥ = snd

 infix  40 ∣_∣

_⁻¹ : {A : Type a} {x y : A} → x ≡ y → y ≡ x
p ⁻¹ = sym p

infix  40 _⁻¹

_∙_ : {A : Type a}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
p ∙ q = trans p q

𝑖𝑑 : (A : Type a) → A → A
𝑖𝑑 A = λ x → x

infixl 30 _∙_

infix 2 ∃-syntax

∃-syntax : ∀ {A : Type a} → (A → Type b) → Set (a ⊔ b)
∃-syntax = ∃

syntax ∃-syntax (λ x → B) = ∃[ x ∈ A ] B

Π : {A : Type a } (B : A → Type b ) → Type (a ⊔ b)
Π {A = A} B = (x : A) → B x

Π-syntax : (A : Type a)(B : A → Type b) → Type (a ⊔ b)
Π-syntax A B = Π B

syntax Π-syntax A (λ x → B) = Π[ x ∈ A ] B
infix 6 Π-syntax

lift∼lower : {A : Type a} → lift ∘ lower ≡ 𝑖𝑑 (Lift b A)
lift∼lower = refl

lower∼lift : {A : Type a} → (lower {a}{b}) ∘ lift ≡ 𝑖𝑑 A
lower∼lift = refl

module _ {a : Level}{A : Type a}{b : Level}{B : A → Type b } where

 _≈_ :  (f g : (a : A) → B a) → Type (a ⊔ b)
 f ≈ g = ∀ x → f x ≡ g x

 infix 8 _≈_

 ≈IsEquivalence : IsEquivalence _≈_
 IsEquivalence.refl   ≈IsEquivalence          = λ _ → refl
 IsEquivalence.sym    ≈IsEquivalence f≈g      = λ x → sym (f≈g x)
 IsEquivalence.trans  ≈IsEquivalence f≈g g≈h  = λ x → trans (f≈g x) (g≈h x)

≡-by-parts :  {A : Type a}{B : Type b}{u v : A × B}
 →            fst u ≡ fst v → snd u ≡ snd v → u ≡ v

≡-by-parts refl refl = refl

transport : {A : Type a } (B : A → Type b) {x y : A} → x ≡ y → B x → B y
transport B refl = id

