---
layout: default
title : "Setoid.Relations module (The Agda Universal Algebra Library)"
date : "2021-09-17"
author: "the agda-algebras development team"
---

## Relations on setoids

This is the [Setoid.Relations][] module of the [Agda Universal Algebra Library][].

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Relations where

open import Setoid.Relations.Discrete    public
open import Setoid.Relations.Quotients   public
open import Setoid.Relations.Continuous  public
open import Setoid.Relations.Properties  public
```
