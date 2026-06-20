---
layout: default
title : "Setoid.Congruences module (Agda Universal Algebra Library)"
date : "2021-09-17"
author: "agda-algebras development team"
---

### Congruences


```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Congruences {𝑆 : Signature 𝓞 𝓥} where

open import Setoid.Congruences.Basic {𝑆 = 𝑆} public
open import Setoid.Congruences.CompleteLattice {𝑆 = 𝑆} public
open import Setoid.Congruences.Generation {𝑆 = 𝑆} public
open import Setoid.Congruences.Lattice {𝑆 = 𝑆}
open import Setoid.Congruences.Properties {𝑆 = 𝑆} public
open import Setoid.Congruences.Permutability {𝑆 = 𝑆} public
```

--------------------------------

<span style="float:left;">[← Setoid.Relations.Quotients](Setoid.Relations.Quotients.html)</span>
<span style="float:right;">[Setoid.Algebras.Basic →](Setoid.Algebras.Basic.html)</span>

{% include UALib.Links.md %}
