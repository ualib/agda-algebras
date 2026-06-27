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

(The two-signature modules [Setoid.Terms.Translation][] and
[Setoid.Terms.Interpretation][] relate two signatures at once, so they are not
`{𝑆}`-parameterized; they are nonetheless re-exported here for convenience.)
