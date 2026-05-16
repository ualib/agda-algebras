---
layout: default
file: "src/Examples/Classical.lagda.md"
title: "Examples.Classical module"
date: "2026-05-15"
author: "the agda-algebras development team"
---

### <a id="examples-classical">Worked examples of classical structures</a>

This is the [Examples.Classical][] module of the [Agda Universal Algebra Library][].

The umbrella for the `Examples/Classical/` subtree, paralleling how `src/Classical.lagda.md` umbrellas the `Classical/` tree.  Re-exports the per-structure example modules.  At present (M3-2) the only such module is `Semigroup`; as Monoid (M3-4), Group (M3-4), Lattice (M3-5), and Ring (M3-6) land, their worked-example siblings will be re-exported here.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Classical where

open import Examples.Classical.Semigroup public
```

--------------------------------------

{% include UALib.Links.md %}
