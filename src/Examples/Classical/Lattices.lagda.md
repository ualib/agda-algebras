---
layout: default
file: "src/Examples/Classical/Lattices.lagda.md"
title: "Examples.Classical.Lattices module"
date: "2026-05-31"
author: "the agda-algebras development team"
---

### Worked examples of lattices {#examples-classical-lattices}

This is the [Examples.Classical.Lattices][] module of the [Agda Universal Algebra Library][].

Barrel for the worked `Lattice` examples under [`Examples/Classical/Lattices/`][].
Each submodule is the home of one concrete lattice: `Two` is the two-element Boolean
lattice `𝟚`, and `L7` is the seven-element lattice of interest in the Finite Lattice
Representation Problem.  Distributive-lattice and Heyting examples live in their own
structure-paired modules ([`Examples.Classical.DistributiveLattice`][],
[`Examples.Classical.HeytingChain3`][]).

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Classical.Lattices where

open import Examples.Classical.Lattices.Two public
open import Examples.Classical.Lattices.L7  public
```

--------------------------------------

<span style="float:left;">[↑ Examples.Classical](Examples.Classical.html)</span>

{% include UALib.Links.md %}
