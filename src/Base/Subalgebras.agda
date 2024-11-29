
{-# OPTIONS --without-K --exact-split --safe #-}

open import Overture using ( Signature ; 𝓞 ; 𝓥 )

module Base.Subalgebras {𝑆 : Signature 𝓞 𝓥} where

open import Base.Subalgebras.Subuniverses  {𝑆 = 𝑆} public
open import Base.Subalgebras.Subalgebras   {𝑆 = 𝑆} public
open import Base.Subalgebras.Properties    {𝑆 = 𝑆} public

