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

module Setoid.Terms where

open import Setoid.Terms.Basic  public
open import Setoid.Terms.Interpretation       public
open import Setoid.Terms.Monad  public
open import Setoid.Terms.Operations  public
open import Setoid.Terms.Properties  public
open import Setoid.Terms.Translation          public
```

(The two-signature modules [Setoid.Terms.Translation][] and
[Setoid.Terms.Interpretation][] relate two signatures at once, so they are not
`{𝑆}`-parameterized; they are nonetheless re-exported here for convenience.)
