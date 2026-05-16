---
layout: default
file: "src/Classical/Small/Structures.lagda.md"
title: "Classical.Small.Structures module"
date: "2026-05-15"
author: "the agda-algebras development team"
---

### <a id="classical-small-structures">Level-fixed classical structures</a>

This is the [Classical.Small.Structures][] module of the [Agda Universal Algebra Library][].

The umbrella for the `Classical/Small/Structures/` subtree.  Re-exports each per-structure `ℓ₀`-veneer; under M3-2 the only such structure is `Semigroup`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Small.Structures where

open import Classical.Small.Structures.Semigroup public
```

--------------------------------------

<span style="float:left;">[← Classical.Small](Classical.Small.html)</span>

{% include UALib.Links.md %}
