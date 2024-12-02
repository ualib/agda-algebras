
{-# OPTIONS --without-K --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Homomorphisms {𝑆 : Signature 𝓞 𝓥} where

open import Setoid.Homomorphisms.Basic              {𝑆 = 𝑆} public
open import Setoid.Homomorphisms.Properties         {𝑆 = 𝑆} public
open import Setoid.Homomorphisms.Kernels            {𝑆 = 𝑆} public
open import Setoid.Homomorphisms.Products           {𝑆 = 𝑆} public
open import Setoid.Homomorphisms.Noether            {𝑆 = 𝑆} public
open import Setoid.Homomorphisms.Factor             {𝑆 = 𝑆} public
open import Setoid.Homomorphisms.Isomorphisms       {𝑆 = 𝑆} public
open import Setoid.Homomorphisms.HomomorphicImages  {𝑆 = 𝑆} public

