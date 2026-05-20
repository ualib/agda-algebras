---
layout: default
file: "src/Classical/Bundles.lagda.md"
title: "Classical.Bundles module"
date: "2026-05-15"
author: "the agda-algebras development team"
---

### <a id="classical-bundles">Stdlib-shaped record bundles for classical structures</a>

This is the [Classical.Bundles][] module of the [Agda Universal Algebra Library][].

The `Classical/Bundles/` subtree houses the record-typed *bundle views* of the
classical structures.  Each per-structure file `Classical/Bundles/X.lagda.md`
declares a record whose fields match the corresponding `Algebra.Bundles.X` in the
Agda standard library, and supplies bidirectional conversion functions between this
record and the canonical Σ-typed core defined in
[`Classical/Structures/X`][Classical.Structures].  The two representations carry the
same mathematical content and round-trip through each other up to the underlying
setoid equivalence; the bundle view exists solely so that code typed against
`Algebra.Bundles` can be reused without writing the stdlib record by hand.

The cost of the bundle view is bounded and predictable: per structure it is one
record definition, two conversion functions, and a round-trip proof.  The design
rationale — including why this is *not* a parallel implementation of the structure
but rather a narrow interop view — is recorded in [ADR-002][ADR-002].

This file is the umbrella for the subtree.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Bundles where

open import Classical.Bundles.Magma public
open import Classical.Bundles.Semigroup public
```

--------------------------------------

<span style="float:left;">[← Classical.Structures](Classical.Structures.html)</span>
<span style="float:right;">[Classical.Small →](Classical.Small.html)</span>

{% include UALib.Links.md %}
