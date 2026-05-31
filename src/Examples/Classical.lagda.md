---
layout: default
file: "src/Examples/Classical.lagda.md"
title: "Examples.Classical module"
date: "2026-05-17"
author: "the agda-algebras development team"
---

### Worked examples of classical structures

This is the [Examples.Classical][] module of the [Agda Universal Algebra Library][].

Worked examples of concrete classical structures live in this subtree, paired
with the per-structure modules under [`Classical/`][Classical].  Each
[`Examples/Classical/X.lagda.md`][] module is the home of worked examples of
structure `X`: canonical first instances, alternative constructions, finite
small cases, examples of failure modes (e.g., a magma that is not a semigroup,
a semigroup that is not a monoid).  The pattern of pairing one canonical first
example with each structure issue is established in M3-3 ([`Examples.Classical.Magma`][])
and continues issue-by-issue under milestone M3.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Classical where

open import Examples.Classical.CommutativeIdempotentMagma public
open import Examples.Classical.CommutativeSemigroup public
open import Examples.Classical.CommutativeMonoid public
open import Examples.Classical.Lattices public
open import Examples.Classical.Magma public
open import Examples.Classical.Monoid public
open import Examples.Classical.Semigroup public
open import Examples.Classical.Semilattice public
```

--------------------------------------

<span style="float:left;">[↑ Examples](Examples.html)</span>

{% include UALib.Links.md %}
