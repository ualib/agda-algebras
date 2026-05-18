---
layout: default
file: "src/Classical/Small/Structures/Magma.lagda.md"
title: "Classical.Small.Structures.Magma module"
date: "2026-05-17"
author: "the agda-algebras development team"
---

### <a id="classical-small-magma">Level-fixed magma veneer</a>

This is the [Classical.Small.Structures.Magma][] module of the [Agda Universal Algebra Library][].

This module specializes [`Classical.Structures.Magma`][] to the common case where
both the carrier level and the equivalence level are `lzero` — Set-valued
carriers with propositional or set-truncated equivalence.  Finite-template CSP
(M7), the finite cases relevant to FLRP intuition (M6), and the tutorial
contexts in [`Examples/`][Examples] and [`Demos/`][Demos] typically live in this
small case; pulling the level-fixed specialization out keeps the polymorphic
core unencumbered while giving downstream consumers a flat import without
universe polymorphism in the foreground.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Small.Structures.Magma where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive  using () renaming ( Set to Type )
open import Level           using ( lzero )

-- Imports from the Agda Universal Algebra Library ----------------------------
import Classical.Structures.Magma as Polymorphic
```

#### <a id="the-type">The level-fixed type</a>

```agda
Magma : Type _
Magma = Polymorphic.Magma lzero lzero
```

#### <a id="fromOp">Small `fromOp`</a>

The polymorphic `fromOp` specializes immediately: with `α = lzero`, it produces
a `Polymorphic.Magma lzero lzero` from `(A : Type lzero) → (A → A → A)`, which
is exactly the level-fixed `Magma` above.

```agda
fromOp : (A : Type lzero) → (A → A → A) → Magma
fromOp = Polymorphic.fromOp
```

--------------------------------------

<span style="float:left;">[← Classical.Small](Classical.Small.html)</span>
<span style="float:right;">[Examples.Classical.Magma →](Examples.Classical.Magma.html)</span>

{% include UALib.Links.md %}
