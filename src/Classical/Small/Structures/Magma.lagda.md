---
layout: default
file: "src/Classical/Small/Structures/Magma.lagda.md"
title: "Classical.Small.Structures.Magma module"
date: "2026-05-17"
author: "the agda-algebras development team"
---

### Level-fixed Magmas

This is the [Classical.Small.Structures.Magma][] module of the [Agda Universal Algebra Library][].

This module specializes [`Classical.Structures.Magma`][] to the common case where the universe
level of both the carrier and the equivalence is `0ℓ` — Set-valued carriers with
propositional or set-truncated equivalence.  Finite-template CSP, the finite cases
relevant to [FLRP][] intuition, and the tutorial contexts in [`Examples/`][Examples]
and [`Demos/`][Demos] typically live in this small case; pulling the
fixed-type-universe-level specialization out keeps the polymorphic core unencumbered
while giving downstream consumers a flat import without universe polymorphism in the
foreground.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Small.Structures.Magma where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive  using () renaming ( Set to Type )
open import Level           using ( 0ℓ ; suc )

-- Imports from the Agda Universal Algebra Library ----------------------------
import Classical.Structures.Magma as Polymorphic
```
-->

#### The level-fixed Magma Type

```agda
Magma : Type (suc 0ℓ)
Magma = Polymorphic.Magma 0ℓ 0ℓ
```

#### Small `opsToMagma`

The polymorphic `opsToMagma` specializes immediately: with `α = 0ℓ`, it produces
a `Polymorphic.Magma 0ℓ 0ℓ` from `(A : Type 0ℓ) → (A → A → A)`, which
is exactly the level-fixed `Magma` above.

```agda
opsToMagma : (A : Type 0ℓ) → (A → A → A) → Magma
opsToMagma A = Polymorphic.opsToMagma {A = A}
```
