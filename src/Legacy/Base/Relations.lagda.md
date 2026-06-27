---
layout: default
title : "Relations module (The Agda Universal Algebra Library)"
date : "2021-01-12"
author: "the agda-algebras development team"
---

## <a id="relations">Relations</a>

This is the [Legacy.Base.Relations][] module of the [Agda Universal Algebra Library][].

In the [Legacy.Base.Relations.Discrete][] submodule we define types that represent *unary* and *binary relations*.

We refer to these as "discrete relations" to contrast them with the "continuous," *general* and *dependent relations* that we introduce in [Legacy.Base.Relations.Continuous][].

We call the latter "continuous relations" because they can have arbitrary arity and they can be defined over arbitrary families of types.

Finally, in [Legacy.Base.Relations.Quotients][] we define quotient types.


```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Legacy.Base.Relations where

open import Legacy.Base.Relations.Discrete    public
open import Legacy.Base.Relations.Continuous  public
open import Legacy.Base.Relations.Properties  public
open import Legacy.Base.Relations.Quotients   public
```
