---
layout: default
title : "Legacy.Base.Subalgebras module (The Agda Universal Algebra Library)"
date : "2021-01-14"
author: "agda-algebras development team"
---

## <a id="subalgebra-types">Subalgebra Types</a>

This is the [Legacy.Base.Subalgebras][] module of the [Agda Universal Algebra Library][].


```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( Signature ; 𝓞 ; 𝓥 )

module Legacy.Base.Subalgebras {𝑆 : Signature 𝓞 𝓥} where

open import Legacy.Base.Subalgebras.Subuniverses  {𝑆 = 𝑆} public
open import Legacy.Base.Subalgebras.Subalgebras   {𝑆 = 𝑆} public
open import Legacy.Base.Subalgebras.Properties    {𝑆 = 𝑆} public
```
