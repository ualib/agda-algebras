---
layout: default
file: "src/Classical/Small/Structures.lagda.md"
title: "Classical.Small.Structures module"
date: "2026-05-17"
author: "the agda-algebras development team"
---

### Aggregator for Level-fixed Structures

This is the [Classical.Small.Structures][] module of the [Agda Universal Algebra Library][].

This is the parallel-to-[`Classical.Structures`][] aggregator inside the
[`Classical.Small`][] subtree.  It re-exports each per-structure level-fixed
veneer in `Classical/Small/Structures/X.lagda.md` as those land under milestone
M3.  See [ADR-002][] for the design rationale.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Small.Structures where

open import Classical.Small.Structures.AbelianGroup public
open import Classical.Small.Structures.CommutativeMonoid public
open import Classical.Small.Structures.CommutativeRing public
open import Classical.Small.Structures.CommutativeSemigroup public
open import Classical.Small.Structures.DistributiveLattice public
open import Classical.Small.Structures.Group public
open import Classical.Small.Structures.Lattice public
open import Classical.Small.Structures.Magma public
open import Classical.Small.Structures.Monoid public
open import Classical.Small.Structures.Ring public
open import Classical.Small.Structures.Semigroup public
open import Classical.Small.Structures.Semilattice public
```
-->
