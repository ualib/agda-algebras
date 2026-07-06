---
layout: default
file: "src/Classical.lagda.md"
title: "Classical module"
date: "2026-05-15"
author: "the agda-algebras development team"
---

## Classical algebraic structures

This is the [Classical][] module of the [Agda Universal Algebra Library][].

The `Classical/` tree formalizes specific algebraic theories — semigroups, monoids,
groups, lattices, rings, and so on — over the universal-algebra foundation laid down
in [`Setoid/`][Setoid] (see [ADR-001][ADR-001]).  The word *classical* names the
long-standing tradition of concrete algebraic structures, as distinct from the
universal-algebraic treatment of algebras-over-a-signature; it carries no commitment
to classical logic, which the library does not assume.  The design of this tree is
recorded in [ADR-002][ADR-002].

### Quintuple-per-structure organization

Each concrete structure `X` ships as a quintuple of files, organized into five parallel subtrees:

+  [`Classical/Signatures`][Classical.Signatures] — the signature `𝑆ₓ` whose operations `X` interprets.

+  [`Classical/Theories`][Classical.Theories] — the set of defining equations `Eₓ`
   that pick `X` out of the class of `𝑆ₓ`-algebras.

+  [`Classical/Structures`][Classical.Structures] — the Σ-typed core
   `X α ρ = Σ[ 𝑨 ∈ Algebra 𝑆ₓ α ρ ] 𝑨 ⊨ Eₓ`, the canonical form for library-internal use.

+  [`Classical/Bundles`][Classical.Bundles] — a parallel record-typed bundle view
   matching the shape of `Algebra.Bundles.X` in the Agda standard library, with
   bidirectional conversion to and from the Σ-typed core.

+  [`Classical/Small`][Classical.Small] — a level-fixed veneer specialized to the
   `ℓ₀`–`ℓ₀` case, for downstream consumers (finite-template CSP, FLRP intuition,
   tutorial contexts) that do not need polymorphism.

The five subtrees above are the *constituent* files of each structure.  A sixth
parallel subtree — [`Classical/Properties`][Classical.Properties] — collects
*derived* results: theorems about a fixed inhabitant of one of the structures (the
order-theoretic view of a lattice, uniqueness of inverses in a group, `0 · x ≈ 0` in
a ring) rather than part of the structure's definition.  Properties is sparser than
the quintuple subtrees; it accretes per structure as concrete derived results land.

The first axis — Signatures, Theories, Structures, Bundles, Small (plus Properties
for derived results) — is orthogonal to the second axis, which is the specific
structure under consideration.


### Cubical portability discipline

Equations in the Σ-typed core are stated purely in terms of the `Algebra.Domain`
setoid equivalence — never in terms of propositional equality or any other
setoid-specific feature.  This discipline makes the eventual port to cubical Agda
([ADR-003][ADR-003]) substitutional rather than rewriting: replacing the setoid
equivalence by the path type and rerunning the type-checker should be sufficient for
most of the tree.

### Scaffold status

This file is the umbrella for the `Classical/` tree.  The five quintuple subtree
aggregators below re-export concrete structures as they land under milestone M3,
and the `Properties` aggregator was added in M3-7 for per-structure
derived-results modules.


<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical where

open import Classical.Bundles          public
open import Classical.Categories       public
open import Classical.Equations        public
open import Classical.Interpretations  public
open import Classical.Operations       public
open import Classical.Properties       public
open import Classical.Signatures       public
open import Classical.Small
open import Classical.Structures       public
open import Classical.Theories         public
```
-->
