---
layout: default
file: "src/Classical/Signatures/Magma.lagda.md"
title: "Classical.Signatures.Magma module"
date: "2026-05-17"
author: "the agda-algebras development team"
---

### <a id="classical-signatures-magma">The signature of magmas</a>

This is the [Classical.Signatures.Magma][] module of the [Agda Universal Algebra Library][].

A *magma* is, traditionally, a carrier equipped with a single binary operation —
the most minimal of the classical algebraic structures, and the right starting
point for the [`Classical/`][Classical] tree because its equational theory is
empty.  This module fixes the signature of magmas as a one-symbol algebraic
signature with that symbol assigned arity `Fin 2`.

Per [ADR-002 v2 §5](../../docs/adr/002-classical-layer-design.md), every concrete
classical structure `X` is characterized by a pair `(Sig-X , Th-X)` — its own
signature and its own complete equational theory in that signature.  For Magma the
theory is empty; the signature carries the whole content.

The conventions for naming established here are *normative* for every subsequent
structure (Semigroup in M3-4, Monoid and Group in M3-6, Lattice in M3-7, Ring in
M3-8); each follows the same `Op-X`/`<symbol>-Op`/`ar-X`/`Sig-X` pattern,
extending or reusing as appropriate.

+  **Operation symbols** are introduced via a one-or-more-constructor data type
   `Op-<Structure>`, with each constructor named `<symbol>-Op` (hyphen-separated,
   capital `O`).  Reserving the bare symbol — `∙`, `ε`, `⁻¹`, `+`, `0`, `·`, `1`,
   `∧`, `∨` — for user-facing curried sugar avoids a name clash between the
   syntactic operation-symbol-of-the-signature and the semantic curried operation
   on a fixed algebra.
+  **Arity functions** are named `ar-<Structure>` and defined by direct pattern
   matching on operation-symbol constructors (`ar-Magma ∙-Op = Fin 2`).  Direct
   pattern matching is required, not optional: the `Classical.Equations` builders
   demand definitional reduction of `ArityOf 𝑆 f` to a concrete `Fin n` at use
   sites, which fails for indirect definitions (table lookups, conditionals).
+  **Signature values** are named `Sig-<Structure>` and assembled as a Σ-pair of
   the operation-symbol type and the arity function.  The hyphenated long form is
   preferred over subscripted alternatives (`𝑆ₘₐ`, `𝑆_Magma`) per
   [ADR-002 v2 §7](../../docs/adr/002-classical-layer-design.md); the long form
   survives grep, copy/paste, and rendering across plain-text channels.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Signatures.Magma where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive using ()                renaming ( Set to Type )
open import Data.Fin.Base  using ( Fin )
open import Data.Product   using ( _,_ )
open import Level          using ( 0ℓ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Signatures using ( Signature )
```

#### <a id="operation-symbols">The operation-symbol type</a>

A magma has a single binary operation symbol.  The constructor is named `∙-Op`
following the `<symbol>-Op` convention; the bare `∙` is reserved for the curried
user-facing accessor introduced in [`Classical.Structures.Magma`][].

```agda
data Op-Magma : Type where
  ∙-Op : Op-Magma
```

#### <a id="arity-function">The arity function</a>

`∙-Op` is binary, so its arity is `Fin 2`.  Direct pattern matching on the single
constructor lets `ArityOf Sig-Magma ∙-Op` reduce definitionally to `Fin 2` —
this is what makes the arity-conformance evidence `refl` of type
`ArityOf Sig-Magma ∙-Op ≡ Fin 2` typecheck in `Th-Semigroup` (M3-4) and every
subsequent theory.

```agda
ar-Magma : Op-Magma → Type
ar-Magma ∙-Op = Fin 2
```

#### <a id="signature-value">The signature value</a>

```agda
Sig-Magma : Signature 0ℓ 0ℓ
Sig-Magma = Op-Magma , ar-Magma
```

--------------------------------------

<span style="float:left;">[← Classical.Signatures](Classical.Signatures.html)</span>
<span style="float:right;">[Classical.Structures.Magma →](Classical.Structures.Magma.html)</span>

{% include UALib.Links.md %}
