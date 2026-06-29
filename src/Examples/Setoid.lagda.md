---
layout: default
file: "src/Examples/Setoid.lagda.md"
title: "Examples.Setoid module"
date: "2026-05-31"
author: "the agda-algebras development team"
---

### Worked examples over the Setoid universal-algebra layer {#examples-setoid}

This is the [Examples.Setoid][] module of the [Agda Universal Algebra Library][].

Whereas [`Examples/Classical/`][] pairs one worked instance with each *concrete
structure* (magma, semigroup, monoid, …), the modules collected here exercise the
generic [`Setoid/`][] universal-algebra machinery directly: free algebras over a
signature, relatively free algebras / presentations, quotients by a congruence, and
Birkhoff's HSP theorem specialized to a concrete algebra.  They are the
cross-structure and "richer" examples requested in
[issue #266](https://github.com/ualib/agda-algebras/issues/266).

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Setoid where

-- Each worked example defines its own local syntactic-product helper `_·_`, so they
-- must be opened without `public`: re-exporting would fail due to name clash.
-- This barrel keeps the five modules in the build and the documentation tree.
open import Examples.Setoid.FreeMagma
open import Examples.Setoid.FreeSemigroup
open import Examples.Setoid.Presentation
open import Examples.Setoid.FiniteQuotient
open import Examples.Setoid.HSPCommutativeMonoid
```
