---
layout: default
title : "Base.Algebras module (Agda Universal Algebra Library)"
date : "2021-01-12"
author: "agda-algebras development team"
---

## <a id="algebra-types">Algebra Types</a>

This is the [Base.Algebras][] module of the [Agda Universal Algebra Library][]
in which we use type theory and [Agda][] to codify the most basic objects of
universal algebra, such as *signatures*, *algebras*, *product algebras*,
*congruence relations*, and *quotient algebras*.


```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture  using ( 𝓞 ; 𝓥 ; Signature )

module Legacy.Base.Algebras {𝑆 : Signature 𝓞 𝓥 } where

open import Legacy.Base.Algebras.Basic        {𝑆 = 𝑆} public
open import Legacy.Base.Algebras.Products     {𝑆 = 𝑆} public
open import Legacy.Base.Algebras.Congruences  {𝑆 = 𝑆} public
```


-------------------------------------

<span style="float:left;">[← Base.Adjunction.Residuation](Base.Adjunction.Residuation.html)</span>
<span style="float:right;">[Base.Algebras.Basic →](Base.Algebras.Basic.html)</span>

{% include UALib.Links.md %}
