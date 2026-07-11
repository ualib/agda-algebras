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
+ `L7` is the seven-element lattice of interest in the Finite Lattice Representation Problem (FLRP).

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Classical.Lattices where

open import Examples.Classical.Lattices.L2
open import Examples.Classical.Lattices.L2Distributive
open import Examples.Classical.Lattices.L3Heyting
open import Examples.Classical.Lattices.L7
```
