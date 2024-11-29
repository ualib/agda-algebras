
{-# OPTIONS --without-K --exact-split --safe #-}

module Base.Functions.Injective where

open import Agda.Primitive                         using () renaming ( Set to Type )
open import Function                               using ( _↣_ ;  _∘_ ; Injective )
open import Function.Construct.Identity            using ( ↣-id )
open import Level                                  using ( _⊔_ ; Level )
open import Relation.Binary                        using ( Rel )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl )

private variable a b c : Level

id-is-injective : {A : Type a} → A ↣ A
id-is-injective {A = A} = ↣-id A

module _ {A : Type a}{B : Type b} where

 IsInjective : (A → B) → Type (a ⊔ b)
 IsInjective f = Injective _≡_ _≡_ f

∘-injective :  {A : Type a}{B : Type b}{C : Type c}{f : A → B}{g : B → C}
  →            IsInjective f → IsInjective g → IsInjective (g ∘ f)

∘-injective fi gi = λ x → fi (gi x)

