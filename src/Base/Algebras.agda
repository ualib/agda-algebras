
{-# OPTIONS --without-K --exact-split --safe #-}

open import Overture  using ( 𝓞 ; 𝓥 ; Signature )

module Base.Algebras {𝑆 : Signature 𝓞 𝓥 } where

open import Base.Algebras.Basic        {𝑆 = 𝑆} public
open import Base.Algebras.Products     {𝑆 = 𝑆} public
open import Base.Algebras.Congruences  {𝑆 = 𝑆} public

