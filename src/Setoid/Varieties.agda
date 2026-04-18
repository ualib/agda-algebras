
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Varieties {𝑆 : Signature 𝓞 𝓥} where

open import Setoid.Varieties.EquationalLogic   {𝑆 = 𝑆} public
open import Setoid.Varieties.SoundAndComplete  {𝑆 = 𝑆} public
open import Setoid.Varieties.Closure           {𝑆 = 𝑆} public
open import Setoid.Varieties.Properties        {𝑆 = 𝑆} public
open import Setoid.Varieties.Preservation      {𝑆 = 𝑆} public
open import Setoid.Varieties.FreeAlgebras      {𝑆 = 𝑆} public
open import Setoid.Varieties.HSP               {𝑆 = 𝑆} public

