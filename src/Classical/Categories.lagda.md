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

+  [Classical.Categories.Forgetful][] upgrades the classical forgetful
   *projections* to forgetful *functors*, supplying the morphism action uniformly
   through the reduct functor of [Setoid.Categories.Reduct][], and closes by
   re-deriving the per-structure theory obligations from the reduct-invariance of
   satisfaction.
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
