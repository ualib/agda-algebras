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

The free lattice on three generators, the diamond `M₃` and the pentagon `N₅`
from their tables, the two-element lattice as a distributive lattice, and the
three-element chain as a Heyting algebra, which this barrel held until October
2026, are worked examples of the library ualib/agda-lattices, which builds on
this one.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Examples.Classical.Lattices where

open import Examples.Classical.Lattices.L2
```
