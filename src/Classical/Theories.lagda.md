---
layout: default
file: "src/Classical/Theories.lagda.md"
title: "Classical.Theories module"
date: "2026-05-15"
author: "the agda-algebras development team"
---

### <a id="classical-theories">Equational theories of classical structures</a>

This is the [Classical.Theories][] module of the [Agda Universal Algebra Library][].

The `Classical/Theories/` subtree houses the per-structure equational theories: for
each concrete structure `X` with signature `𝑆ₓ`, a set `Eₓ` of `𝑆ₓ`-equations that
picks the `X`-models out of the class of all `𝑆ₓ`-algebras.  Each
`Classical/Theories/X.lagda.md` module defines `Eₓ` and re-exports it through this
umbrella.

By convention the equations are stated in terms of the `Algebra.Domain` setoid
equivalence rather than any setoid-specific feature without a cubical analog, so that
the eventual port to cubical Agda ([ADR-003][ADR-003]) is mechanical.  The design
rationale is recorded in [ADR-002][ADR-002].

This file is the umbrella for the subtree; at the moment this scaffold lands the
subtree is empty.  Concrete theory modules arrive issue-by-issue under milestone M3
(M3-2 onward), pairing with the corresponding `Classical/Signatures/X.lagda.md` and
consumed by `Classical/Structures/X.lagda.md`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Theories where

open import Classical.Theories.Semigroup public
```

--------------------------------------

<span style="float:left;">[← Classical.Signatures](Classical.Signatures.html)</span>
<span style="float:right;">[Classical.Structures →](Classical.Structures.html)</span>

{% include UALib.Links.md %}
