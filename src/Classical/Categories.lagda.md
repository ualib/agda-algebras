---
layout: default
file: "src/Classical/Categories.lagda.md"
title: "Classical.Categories module"
date: "2026-06-11"
author: "the agda-algebras development team"
---

### Category theory of classical structures

This is the [Classical.Categories][] module of the [Agda Universal Algebra Library][].

This is a barrel module: it declares nothing of its own and re-exports the two
modules that give the classical structures their categorical face.

+  [Classical.Categories.Forgetful][] upgrades a classical forgetful
   *projection* to a forgetful *functor*, supplying the morphism action through
   the reduct functor of [Setoid.Categories.Reduct][].  The one instance so far
   is `monoid→semigroupF`; the module closes by re-deriving that functor's
   theory obligation from reduct-invariance of satisfaction, the general lemma
   of which the bespoke per-structure pivots are instances.
+  [Classical.Categories.AdjoinUnit][] proves the inaugural free-expansion
   adjunction: freely adjoining a unit to a semigroup (the free monoid on a
   semigroup, with carrier `Maybe 𝕌[ 𝑺 ]`) is left adjoint to the
   monoid-to-semigroup forgetful, with unit, counit, both naturality squares, the
   triangle identities, and the explicit universal property.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Categories where

open import Classical.Categories.AdjoinUnit public
open import Classical.Categories.Forgetful public
```
