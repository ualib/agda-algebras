
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Terms {𝑆 : Signature 𝓞 𝓥} where

open import Setoid.Terms.Basic       {𝑆 = 𝑆} public
open import Setoid.Terms.Properties  {𝑆 = 𝑆} public
open import Setoid.Terms.Operations  {𝑆 = 𝑆} public

