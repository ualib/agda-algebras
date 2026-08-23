---
layout: default
title : "Setoid.Varieties.Maltsev module (Agda Universal Algebra Library)"
date : "2021-07-26"
author: "agda-algebras development team"
---

### Maltsev Conditions

This is the [Setoid.Varieties.Maltsev][] module of the [Agda Universal Algebra Library][].

A **Maltsev condition** is a demand for terms satisfying prescribed identities,
and the point of the notion is that such a demand implies a property of the
congruence lattice of every algebra in the variety.  Conditions of this shape are
how lattice-theoretic facts about congruences become checkable by exhibiting
terms.

The original example is Maltsev's own, and it is the one formalised here: a
*Maltsev term* is a ternary `m` satisfying `m x x y ≈ y` and `m x y y ≈ x`, and a
variety with one is congruence-permutable.  Following
[Setoid.Varieties.Interpretation][], the demand is posed not as a bare term but as
a *theory interpretation*: `Th-Maltsev` is the two-equation theory over the
one-ternary-symbol signature `Sig-Maltsev`, and `HasMaltsevTerm ℰ` is
`Th-Maltsev ≼ ℰ`, so "`ℰ` admits a Maltsev term" is literally "the Maltsev theory
interprets into `ℰ`".

This is a barrel module, re-exporting [Setoid.Varieties.Maltsev.Basic][] for the
general setting, and [Setoid.Varieties.Maltsev.Permutability][],
[Setoid.Varieties.Maltsev.Distributivity][] and
[Setoid.Varieties.Maltsev.Modularity][] for the three classical conditions.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Varieties.Maltsev where

open import Setoid.Varieties.Maltsev.Basic           public
open import Setoid.Varieties.Maltsev.Permutability   public
open import Setoid.Varieties.Maltsev.Distributivity  public
open import Setoid.Varieties.Maltsev.Modularity      public
```
