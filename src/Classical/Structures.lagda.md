---
layout: default
file: "src/Classical/Structures.lagda.md"
title: "Classical.Structures module"
date: "2026-05-15"
author: "the agda-algebras development team"
---

### Σ-typed cores of classical structures

This is the [Classical.Structures][] module of the [Agda Universal Algebra Library][].

The `Classical/Structures/` subtree houses the Σ-typed cores — the canonical
library-internal representation of each classical structure.  For each concrete `X`
with signature `𝑆ₓ` (from [`Classical/Signatures/X`][Classical.Signatures]) and
equational theory `Eₓ` (from [`Classical/Theories/X`][Classical.Theories]), the core
is

    X : (α ρ : Level) → Type _
    X α ρ = Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ Eₓ

which means `X` is an algebra equipped with a proof that it satisfies the `X`-theory.
The Σ formulation is natural and robust under the eventual cubical port: no theorem
in this subtree depends on setoid-specific machinery, so substituting the path-type
equivalence for the setoid equivalence is a search-and-replace operation rather than
a rewrite.  The full rationale is recorded in [ADR-002][ADR-002].

Each per-structure file `Classical/Structures/X.lagda.md` also ships named
convenience accessors (`Domain`, `Signature`, `equations`) that offset the use-site
ergonomic cost of Σ-projection against the named-field projection a record would have
provided.  Bidirectional bridges to a stdlib-shaped record view are provided in the
parallel [`Classical/Bundles/`][Classical.Bundles] subtree.

This file is the umbrella for the subtree.  The concrete `Magma` and `Semigroup`
submodules are the initial, pattern-setting structures.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures where

open import Classical.Structures.CommutativeMonoid public
open import Classical.Structures.CommutativeSemigroup public
open import Classical.Structures.CommutativeRing public
open import Classical.Structures.DistributiveLattice public
open import Classical.Structures.Group public
open import Classical.Structures.Interpret public
open import Classical.Structures.Lattice public
open import Classical.Structures.Magma public
open import Classical.Structures.Monoid public
open import Classical.Structures.Ring public
open import Classical.Structures.Semigroup public
open import Classical.Structures.Semilattice public
```
