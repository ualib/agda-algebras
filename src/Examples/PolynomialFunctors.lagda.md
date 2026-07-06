---
layout: default
title : "Examples.PolynomialFunctors module"
date : "2026-05-09"
author: "the agda-algebras development team"
---

### Polynomial-functor examples

This is the [Examples.PolynomialFunctors][] module of the [Agda Universal Algebra Library][].

This subtree is illustrative.  It develops a closed-universe encoding of polynomial
functors and their least fixed points (W-types), using the polymorphic-list datatype
as a worked example demonstrating the equivalence between the W-type encoding `μ (L
A)` and the standard inductive definition.  The content was relocated here under #306
from `Legacy.Base.Categories.*`; nothing in the canonical `Setoid/`, `Classical/`, or
planned `Cubical/` development depends on it.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.PolynomialFunctors where

open import Examples.PolynomialFunctors.Functors public
```
