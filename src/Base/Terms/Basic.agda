
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (Signature ; 𝓞 ; 𝓥 )

module Base.Terms.Basic {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive         using () renaming ( Set to Type )
open import Data.Product           using ( _,_ )
open import Level                  using ( Level )

open import Overture          using ( ∣_∣ ; ∥_∥ )
open import Base.Algebras {𝑆 = 𝑆}  using ( Algebra ; ov )

private variable χ : Level

data Term (X : Type χ ) : Type (ov χ)  where
 ℊ : X → Term X    -- (ℊ for "generator")
 node : (f : ∣ 𝑆 ∣)(t : ∥ 𝑆 ∥ f → Term X) → Term X

open Term

𝑻 : (X : Type χ ) → Algebra (ov χ)
𝑻 X = Term X , node

