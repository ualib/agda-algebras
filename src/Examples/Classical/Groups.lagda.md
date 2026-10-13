---
layout: default
file: "src/Examples/Classical/Groups.lagda.md"
title: "Examples.Classical.Groups module"
date: "2026-05-31"
author: "the agda-algebras development team"
---

### Worked examples of groups {#examples-classical-groups}

This is the [Examples.Classical.Groups][] module of the [Agda Universal Algebra Library][].

Index of the worked group examples under `Examples/Classical/Groups/`.  This
module opens each submodule it imports (`open import`, without `public`), so that
the family type-checks from a single entry point, and it deliberately does *not*
re-export their contents.  The finite examples each introduce a local operation
`_·_` and their own characteristic lemmas, which are meaningful only within their
own module, so there is nothing to gain (and names to clash) from re-exporting
them through a barrel.

+ `CyclicGroup` and `AbelianGroup` present `(ℤ, +, 0, -)` — the infinite cyclic group — as a group and as an abelian group.
+ `CyclicGroup3` is the cyclic group `ℤ/3ℤ`, built from a Cayley table.
+ `CyclicGroup6` is the cyclic group `ℤ/6ℤ`, checked to be the direct product `ℤ/2ℤ × ℤ/3ℤ` with the theory of direct decompositions.
+ `KleinFourGroup` is the Klein four-group `V₄`.
+ `SymmetricGroup3` is the symmetric group `S₃`, the smallest non-abelian group.
+ [Examples.Classical.Groups.AlternatingGroup5][] is the alternating group `A₅`,
  the smallest nonabelian simple group, certified simple by finite computation
  from its generated companion [Examples.Classical.Groups.AlternatingGroup5.Tables][].
  This barrel does not import it.  The two modules take several seconds each to
  check, longer than any other module of the library, and a barrel leaves out
  such slow modules so that importing it stays cheap.  `make check` still checks
  both, and either can be imported directly.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Examples.Classical.Groups where

open import Examples.Classical.Groups.AbelianGroup
open import Examples.Classical.Groups.CyclicGroup
open import Examples.Classical.Groups.CyclicGroup3
open import Examples.Classical.Groups.CyclicGroup6
open import Examples.Classical.Groups.KleinFourGroup
open import Examples.Classical.Groups.SymmetricGroup3
```
