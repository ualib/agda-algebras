---
layout: default
title : "Order module (Agda Universal Algebra Library)"
date : "2026-06-02"
author: "agda-algebras development team"
---

### Order-theoretic structures

This is the [Order][] module of the [Agda Universal Algebra Library][].

This top-level `Order/` tree collects the *order-theoretic* structures used across the
universal-algebra development — currently the complete lattice (`Order.CompleteLattice`),
which the standard library lacks.  It is deliberately separate from `Classical/`: here a
lattice is an *ordered* structure (a poset with meets and joins), whereas the
`Classical.*.Lattice` modules formalize lattices *as equational algebras* over
`Sig-Lattice`.  The congruence lattice ([Setoid.Congruences.CompleteLattice][]) and the
subalgebra lattice ([Setoid.Subalgebras.CompleteLattice][]) are the motivating
instances.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Order where

open import Order.CompleteLattice public
```
