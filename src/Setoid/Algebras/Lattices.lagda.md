---
layout: default
title : "Setoid.Algebras.Lattices module (Agda Universal Algebra Library)"
date : "2026-06-02"
author: "agda-algebras development team"
---

### Order-theoretic Lattices in the Algebras tree

This is the [Setoid.Algebras.Lattices][] module of the [Agda Universal Algebra Library][].

This is an umbrella module re-exporting the order-theoretic lattice structures used
across the universal-algebra development (currently the complete lattice; the
congruence and subalgebra lattices are the motivating instances).

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Algebras.Lattices where

open import Setoid.Algebras.Lattices.CompleteLattice public
```

--------------------------------

<span style="float:left;">[← Setoid.Algebras.Congruences](Setoid.Algebras.Congruences.html)</span>
<span style="float:right;">[Setoid.Algebras.Lattices.CompleteLattice →](Setoid.Algebras.Lattices.CompleteLattice.html)</span>

{% include UALib.Links.md %}
