
{-# OPTIONS --without-K --exact-split --safe #-}
module Base.Functions.Inverses where

open import Agda.Primitive    using () renaming ( Set to Type )
open import Data.Product      using ( _,_ ; Σ-syntax )
open import Level             using ( Level ; _⊔_ )
open import Relation.Binary.PropositionalEquality
                              using ( _≡_ ; sym ; refl )
open import Relation.Unary    using ( Pred ; _∈_ )

open import Overture.Basic using ( ∃-syntax ; ∣_∣ )

private variable a b : Level

module _ {A : Type a}{B : Type b} where

 data Image_∋_ (f : A → B) : B → Type (a ⊔ b) where
  eq : {b : B} → (a : A) → b ≡ f a → Image f ∋ b

 open Image_∋_

 Range : (A → B) → Pred B (a ⊔ b)
 Range f b = ∃[ a ∈ A ] (f a) ≡ b

 range : (A → B) → Type (a ⊔ b)
 range f = Σ[ b ∈ B ] ∃[ a ∈ A ](f a) ≡ b

 Image⊆Range : (f : A → B) → ∀ b → Image f ∋ b → b ∈ Range f
 Image⊆Range f b (eq a x) = a , (sym x)

 Range⊆Image : (f : A → B) → ∀ b → b ∈ Range f → Image f ∋ b
 Range⊆Image f b (a , x) = eq a (sym x)

 Imagef∋f : {f : A → B}{a : A} → Image f ∋ (f a)
 Imagef∋f = eq _ refl

 f∈range : {f : A → B}(a : A) → range f
 f∈range {f} a = (f a) , (a , refl)

 Inv : (f : A → B){b : B} → Image f ∋ b  →  A
 Inv f (eq a _) = a

 [_]⁻¹ : (f : A → B) → range f →  A
 [ f ]⁻¹ (_ , (a , _)) = a

 InvIsInverseʳ : {f : A → B}{b : B}(q : Image f ∋ b) → f(Inv f q) ≡ b
 InvIsInverseʳ (eq _ p) = sym p

 ⁻¹IsInverseʳ : {f : A → B}{bap : range f} → f ([ f ]⁻¹ bap) ≡ ∣ bap ∣
 ⁻¹IsInverseʳ {bap = (_ , (_ , p))} = p

 InvIsInverseˡ : ∀ {f a} → Inv f {b = f a} Imagef∋f ≡ a
 InvIsInverseˡ = refl

 ⁻¹IsInverseˡ : ∀ {f a} → [ f ]⁻¹ (f∈range a) ≡ a
 ⁻¹IsInverseˡ = refl

