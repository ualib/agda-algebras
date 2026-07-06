---
layout: default
file: "src/Classical/Small.lagda.md"
title: "Classical.Small module"
date: "2026-05-15"
author: "the agda-algebras development team"
---

### Level-fixed veneers of classical structures

This is the [Classical.Small][] module of the [Agda Universal Algebra Library][].

The `Classical/Small/` subtree houses level-fixed specializations of the polymorphic
structure cores in [`Classical/Structures/`][Classical.Structures].  For each
concrete `X`, the small veneer `Classical/Small/Structures/X.lagda.md` fixes both the
carrier-level `α` and the equivalence-level `ρ` to `ℓ₀`, giving a one-import path for
downstream consumers that do not need universe polymorphism.

The intended audience is the family of downstream developments where most concrete
instances live at `Set` rather than at a polymorphic `Set α` / `Set ρ` family: the
finite-template constraint-satisfaction work in M7, the finite cases that motivate
FLRP intuition in M6, and the tutorial-pedagogical contexts in `Examples/` and
`Demos/`.  The polymorphism in the core is necessary for the substantive theorems but
is a distraction at use sites for the small case; pulling the level-fixed
specialization into its own subtree keeps the polymorphic core unencumbered while
giving small-case users a flat import.  The design rationale is recorded in
[ADR-002][ADR-002].

This file is the umbrella for the subtree, the submodules of which include
fixed-universe-level veneers; these are paired with polymorphic cores in
`Classical/Structures/`.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Small where

open import Classical.Small.Structures public
```
-->
