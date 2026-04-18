
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Algebras {𝑆 : Signature 𝓞 𝓥} where

open import Setoid.Algebras.Basic        {𝑆 = 𝑆} public
open import Setoid.Algebras.Products     {𝑆 = 𝑆} public
open import Setoid.Algebras.Congruences  {𝑆 = 𝑆} public

