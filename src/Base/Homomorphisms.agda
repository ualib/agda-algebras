
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (Signature ; 𝓞 ; 𝓥 )

module Base.Homomorphisms {𝑆 : Signature 𝓞 𝓥} where

open import Base.Homomorphisms.Basic              {𝑆 = 𝑆} public
open import Base.Homomorphisms.Properties         {𝑆 = 𝑆} public
open import Base.Homomorphisms.Kernels            {𝑆 = 𝑆} public
open import Base.Homomorphisms.Products           {𝑆 = 𝑆} public
open import Base.Homomorphisms.Noether            {𝑆 = 𝑆} public
open import Base.Homomorphisms.Factor             {𝑆 = 𝑆} public
open import Base.Homomorphisms.Isomorphisms       {𝑆 = 𝑆} public
open import Base.Homomorphisms.HomomorphicImages  {𝑆 = 𝑆} public

