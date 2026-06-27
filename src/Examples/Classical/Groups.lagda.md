---
layout: default
file: "src/Examples/Classical/Groups.lagda.md"
title: "Examples.Classical.Groups module"
date: "2026-05-31"
author: "the agda-algebras development team"
---

### Worked examples of groups {#examples-classical-groups}

This is the [Examples.Classical.Groups][] module of the [Agda Universal Algebra Library][].

Index of the worked group examples under [`Examples/Classical/Groups/`][].  This
module merely `import`s each submodule, so that the whole family type-checks at once
from a single entry point; it deliberately does *not* `open` or re-export their
contents.  The finite examples each introduce a local operation `_·_` and their own
characteristic lemmas, which are meaningful only within their own module, so there is
nothing to gain (and names to clash) from re-exporting them through a barrel.

+ `CyclicGroup` and `AbelianGroup` present `(ℤ, +, 0, -)` — the infinite cyclic group — as a group and as an abelian group.
+ `CyclicGroup3` is the cyclic group `ℤ/3ℤ`, built from a Cayley table.
+ `KleinFourGroup` is the Klein four-group `V₄`.
+ `SymmetricGroup3` is the symmetric group `S₃`, the smallest non-abelian group.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Classical.Groups where

```

--------------------------------------

<span style="float:left;">[↑ Examples.Classical](Examples.Classical.html)</span>

{% include UALib.Links.md %}
