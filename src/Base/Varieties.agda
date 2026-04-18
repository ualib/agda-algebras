
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( Signature ; 𝓞 ; 𝓥 )

module Base.Varieties {𝑆 : Signature 𝓞 𝓥} where

open import Base.Varieties.EquationalLogic  {𝑆 = 𝑆} public
open import Base.Varieties.Closure          {𝑆 = 𝑆} public
open import Base.Varieties.Properties       {𝑆 = 𝑆} public
open import Base.Varieties.Preservation     {𝑆 = 𝑆} public

open import Level using ( Level )

module _ {α : Level} where

 open import Base.Varieties.FreeAlgebras  {α = α} {𝑆 = 𝑆} public

