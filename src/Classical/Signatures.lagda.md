---
layout: default
file: "src/Classical/Signatures.lagda.md"
title: "Classical.Signatures module"
date: "2026-05-15"
author: "the agda-algebras development team"
---

### <a id="classical-signatures">Signatures of classical structures</a>

This is the [Classical.Signatures][] module of the [Agda Universal Algebra Library][].

The `Classical/Signatures/` subtree houses the per-structure signature definitions for the classical-structures tree.  Each concrete structure `X` carries a fixed signature `𝑆ₓ : Signature 𝓞 𝓥` whose sort `Op` enumerates the operation symbols of `X` together with their arities, defined in a module `Classical/Signatures/X.lagda.md` and re-exported from this umbrella.  The design rationale — Σ-typed cores over signature-equation pairs, with record-typed bundle views for stdlib interop — is recorded in [ADR-002][ADR-002].

This file is the umbrella for the subtree; at the moment this scaffold lands the subtree is empty.  Concrete signature modules arrive issue-by-issue under milestone M3 (M3-2 onward).

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Signatures where

-- Per-structure signature modules will be re-exported here as they land
-- under milestone M3-2 onward; e.g., once M3-2 introduces the
-- semigroup signature, we'll add
--
--   open import Classical.Signatures.Semigroup public
--
-- with analogous lines for Monoid, Group, Lattice, Ring, etc.
```

--------------------------------------

<span style="float:left;">[← Classical](Classical.html)</span>
<span style="float:right;">[Classical.Theories →](Classical.Theories.html)</span>

{% include UALib.Links.md %}
