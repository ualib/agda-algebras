---
layout: default
title : "Setoid.Varieties.Maltsev module (Agda Universal Algebra Library)"
date : "2021-07-26"
author: "agda-algebras development team"
---

### Maltsev Conditions

This is the [Setoid.Varieties.Maltsev][] module of the [Agda Universal Algebra Library][].

A **Maltsev condition** is an identity, or set of identities, between terms of a
variety of algebras, and the point of the notion is that, when such a condition
holds, so do certain properties of the congruence lattice of every algebra in the
variety.  Conditions of this shape are how lattice-theoretic facts about
congruences become checkable by exhibiting terms.

The original example is Maltsev's own; it formalized in the library, along with a
few others like it.  A *Maltsev term* is a ternary `m` satisfying `m x x y ≈ y`
and `m x y y ≈ x`, and a variety with such a term is *congruence-permutable*.
Following [Setoid.Varieties.Interpretation][], the condition is posed not as a
bare term but as a *theory interpretation*: `Th-Maltsev` is the two-equation
theory over the one-ternary-symbol signature `Sig-Maltsev`, and `HasMaltsevTerm ℰ`
is `Th-Maltsev ≼ ℰ`, so "`ℰ` admits a Maltsev term" is literally "the Maltsev theory
interprets into `ℰ`".

This is a barrel module, re-exporting [Setoid.Varieties.Maltsev.Basic][] for the
general setting, along with three modules proving classical theorems involving
Maltsev conditions:

+  [Setoid.Varieties.Maltsev.Permutability][] (Maltsev's theorem),
+  [Setoid.Varieties.Maltsev.Distributivity][] (Jonsson's theorem),
+  [Setoid.Varieties.Maltsev.Modularity][] (Day's theorem).

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Varieties.Maltsev where

open import Setoid.Varieties.Maltsev.Basic           public
open import Setoid.Varieties.Maltsev.Permutability   public
open import Setoid.Varieties.Maltsev.Distributivity  public
open import Setoid.Varieties.Maltsev.Modularity      public
```
