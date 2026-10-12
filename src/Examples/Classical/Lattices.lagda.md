---
layout: default
file: "src/Examples/Classical/Lattices.lagda.md"
title: "Examples.Classical.Lattices module"
date: "2026-05-31"
author: "the agda-algebras development team"
---

### Worked examples of lattices {#examples-classical-lattices}

This is the [Examples.Classical.Lattices][] module of the [Agda Universal Algebra Library][].

Barrel for the worked `Lattice` examples under `Examples/Classical/Lattices/`.
Each submodule is the home of one concrete lattice.

+ `L2` is the two-element Boolean lattice.
+ `L2Distributive` is the two-element Boolean lattice as a `DistributiveLattice`.
+ `L3Heyting` is the three-element chain as a Heyting algebra.
+ `FreeLattice3` is the free lattice on three generators, in which Whitman's
  procedure decides inequalities by evaluation.
+ `M3` is the diamond `M₃`, the five-element modular lattice that is not
  distributive, given by its tables; it satisfies Whitman's condition and
  neither semidistributive law.
+ `N5` is the pentagon `N₅`, given by its tables, which is semidistributive and
  satisfies Whitman's condition.
+ `Nullstellen` is the first datum of McNulty's free-lattice Nullstellensatz
  problem: an equation over `FL(3)` in the closure of another, by meet
  semidistributivity, and outside the congruence it generates, by `M₃`.
+ [Examples.Classical.Lattices.DeansProblem][] checks Freese's example toward
  Dean's problem: two triples in `FL(9)`, each freely generating a copy of
  `FL(3)`, the first sublattice properly inside the second.  This barrel does not
  import it, because its check takes about 12 seconds, far longer than any other
  module's, and a barrel leaves out such slow modules so that importing it stays
  cheap.  `make check` still checks it, and it can be imported directly.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Examples.Classical.Lattices where

open import Examples.Classical.Lattices.L2
open import Examples.Classical.Lattices.L2Distributive
open import Examples.Classical.Lattices.L3Heyting
open import Examples.Classical.Lattices.FreeLattice3
open import Examples.Classical.Lattices.M3
open import Examples.Classical.Lattices.N5
open import Examples.Classical.Lattices.Nullstellen
```
