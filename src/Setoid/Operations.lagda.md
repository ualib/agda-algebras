---
layout: default
title : "Setoid.Operations module (The Agda Universal Algebra Library)"
date : "2026-06-21"
author: "the agda-algebras development team"
---

## Operations on setoids

This is the [Setoid.Operations][] module of the [Agda Universal Algebra Library][].

It collects the setoid-level companions to the operation utilities of
[Overture.Operations][].  At present this is the single submodule
[Setoid.Operations.Properties][], which generalizes the finite, propositional
law-checkers of [Overture.Operations.Properties][] to an arbitrary decidable setoid
equipped with an exhaustive-search witness for its carrier.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Operations where

open import Setoid.Operations.Properties  public
```
