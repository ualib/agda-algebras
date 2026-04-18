
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (Signature ; 𝓞 ; 𝓥 )

module Base.Terms {𝑆 : Signature 𝓞 𝓥} where

open import Base.Terms.Basic       {𝑆 = 𝑆} public
open import Base.Terms.Properties  {𝑆 = 𝑆} public
open import Base.Terms.Operations  {𝑆 = 𝑆} public

