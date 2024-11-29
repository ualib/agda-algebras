
{-# OPTIONS --without-K --exact-split --safe #-}

module Overture.Operations where

open import Agda.Primitive               using () renaming ( Set to Type )
open import Level                        using ( Level ; _⊔_ )

private variable a b ρ 𝓥 : Level

Op : Type a → Type 𝓥 → Type (a ⊔ 𝓥)
Op A I = (I → A) → A

π : {I : Type 𝓥} {A : Type a } → I → Op A I
π i = λ x → x i

arity[_] : {I : Type 𝓥} {A : Type a } → Op A I → Type 𝓥
arity[_] {I = I} f = I

