---
layout: default
title : "Setoid.Varieties module (Agda Universal Algebra Library)"
date : "2021-07-26"
author: "agda-algebras development team"
---

### <a id="equations-and-varieties-for-setoids">Equations and Varieties for Setoids</a>

This is the [Setoid.Varieties][] module of the [Agda Universal Algebra Library][].


```agda


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
```


--------------------------------

<span style="float:left;">[← Setoid.Subalgebras.Properties](Setoid.Subalgebras.Properties.html)</span>
<span style="float:right;">[Setoid.Varieties.EquationalLogic →](Setoid.Varieties.EquationalLogic.html)</span>

{% include UALib.Links.md %}
