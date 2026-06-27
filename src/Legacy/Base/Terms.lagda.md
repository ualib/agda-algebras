---
layout: default
title : "Legacy.Base.Terms module (The Agda Universal Algebra Library)"
date : "2021-01-14"
author: "agda-algebras development team"
---

## <a id="types-for-terms">Types for Terms</a>

This is the [Legacy.Base.Terms][] module of the [Agda Universal Algebra Library][].


```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (Signature ; 𝓞 ; 𝓥 )

module Legacy.Base.Terms {𝑆 : Signature 𝓞 𝓥} where

open import Legacy.Base.Terms.Basic       {𝑆 = 𝑆} public
open import Legacy.Base.Terms.Properties  {𝑆 = 𝑆} public
open import Legacy.Base.Terms.Operations  {𝑆 = 𝑆} public
```
