---
layout: default
file: "src/Classical/Structures.lagda.md"
title: "Classical.Structures module"
date: "2026-05-15"
author: "the agda-algebras development team"
---

### <a id="classical-structures">Σ-typed cores of classical structures</a>

This is the [Classical.Structures][] module of the [Agda Universal Algebra Library][].

The `Classical/Structures/` subtree houses the Σ-typed cores — the canonical library-internal representation of each classical structure.  For each concrete `X` with signature `𝑆ₓ` (from [`Classical/Signatures/X`][Classical.Signatures]) and equational theory `Eₓ` (from [`Classical/Theories/X`][Classical.Theories]), the core is

```text
X : (α ρ : Level) → Type _
X α ρ = Σ[ 𝑨 ∈ Algebra 𝑆ₓ α ρ ] 𝑨 ⊨ Eₓ
```

— "an `X` is an `𝑆ₓ`-algebra equipped with a proof that it satisfies the `X`-theory."  The Σ formulation reads mathematically as the universal algebraist thinks, and is robust under the eventual cubical port: no theorem in this subtree may reach for setoid-specific machinery, so substituting the path-type equivalence for the setoid equivalence is a search-and-replace operation rather than a rewrite.  The full rationale is recorded in [ADR-002][ADR-002].

Each per-structure file `Classical/Structures/X.lagda.md` also ships named convenience accessors (`Domain`, `Signature`, `equations`) that offset the use-site ergonomic cost of Σ-projection against the named-field projection a record would have provided.  Bidirectional bridges to a stdlib-shaped record view live in the parallel [`Classical/Bundles/`][Classical.Bundles] subtree.

This file is the umbrella for the subtree; at the moment this scaffold lands the subtree is empty.  Concrete structure cores arrive issue-by-issue under milestone M3 (M3-2 onward), with `Semigroup` as the pattern-setting first structure.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures where

-- Per-structure Σ-typed core modules will be re-exported here as they
-- land under milestone M3-2 onward; e.g., once M3-2 lands, we'll add
--
--   open import Classical.Structures.Semigroup public
--
-- with analogous lines for Monoid, Group, Lattice, Ring, etc.
```

--------------------------------------

<span style="float:left;">[← Classical.Theories](Classical.Theories.html)</span>
<span style="float:right;">[Classical.Bundles →](Classical.Bundles.html)</span>

{% include UALib.Links.md %}
