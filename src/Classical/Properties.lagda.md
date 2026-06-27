---
layout: default
file: "src/Classical/Properties.lagda.md"
title: "Classical.Properties module"
date: "2026-05-28"
author: "the agda-algebras development team"
---

### Derived properties of classical structures

This is the [Classical.Properties][] module of the [Agda Universal Algebra Library][].

The `Classical/Properties/` subtree houses *derived* results about classical
structures — theorems that are properties of a fixed inhabitant of one of the
structures defined in [`Classical/Structures/`][Classical.Structures], rather
than part of the structure's definition.  Each per-structure file
`Classical/Properties/X.lagda.md` consumes `X-Op`'s curried accessors and
proves further facts about a parameterized `(𝑿 : X α ρ)`.

The inaugural inhabitant is `Classical.Properties.Lattice`, which proves the
order-theoretic view of a lattice.  Future inhabitants include, for example,
uniqueness of inverses in Group and `0 · x ≈ 0` in Ring.

This file is the umbrella for the subtree.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Properties where

open import Classical.Properties.Lattice public
```
