
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Subalgebras {𝑆 : Signature 𝓞 𝓥} where

open import Setoid.Subalgebras.Subuniverses  {𝑆 = 𝑆} public
open import Setoid.Subalgebras.Subalgebras   {𝑆 = 𝑆} public
open import Setoid.Subalgebras.Properties    {𝑆 = 𝑆} public

