---
layout: default
title : "Setoid.Terms module (The Agda Universal Algebra Library)"
date : "2021-09-18"
author: "agda-algebras development team"
---

### Terms on setoids

This is the [Setoid.Terms][] module of the [Agda Universal Algebra Library][].


```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Terms {𝑆 : Signature 𝓞 𝓥} where

open import Setoid.Terms.Basic {𝑆 = 𝑆}       public
open import Setoid.Terms.Interpretation      public
open import Setoid.Terms.Monad {𝑆 = 𝑆}       public
open import Setoid.Terms.Operations {𝑆 = 𝑆}  public
open import Setoid.Terms.Properties {𝑆 = 𝑆}  public
open import Setoid.Terms.Translation         public
```

(The laws of term *translation* along a signature morphism live in
[Setoid.Terms.Translation][]; that module relates two signatures at once, so it is
not `{𝑆}`-parameterized and is imported directly rather than re-exported here.)


--------------------------------

<span style="float:left;">[← Setoid.Homomorphisms.HomomorphicImages](Setoid.Homomorphisms.HomomorphicImages.html)</span>
<span style="float:right;">[Setoid.Terms.Basic →](Setoid.Terms.Basic.html)</span>

{% include UALib.Links.md %}
