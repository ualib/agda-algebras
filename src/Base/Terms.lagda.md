---
layout: default
title : "Base.Terms module (The Agda Universal Algebra Library)"
date : "2021-01-14"
author: "agda-algebras development team"
---

## <a id="types-for-terms">Types for Terms</a>

This is the [Base.Terms][] module of the [Agda Universal Algebra Library][].


```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (Signature ; 𝓞 ; 𝓥 )

module Base.Terms {𝑆 : Signature 𝓞 𝓥} where

open import Base.Terms.Basic       {𝑆 = 𝑆} public
open import Base.Terms.Properties  {𝑆 = 𝑆} public
open import Base.Terms.Operations  {𝑆 = 𝑆} public
```


-------------------------------------

<span style="float:left;">[← Base.Homomorphisms.HomomorphicImages](Base.Homomorphisms.HomomorphicImages.html)</span>
<span style="float:right;">[Base.Terms.Basic →](Base.Terms.Basic.html)</span>

{% include UALib.Links.md %}
