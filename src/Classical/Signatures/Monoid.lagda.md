---
layout: default
file: "src/Classical/Signatures/Monoid.lagda.md"
title: "Classical.Signatures.Monoid module"
date: "2026-05-22"
author: "the agda-algebras development team"
---

### The signature of monoids

This is the [Classical.Signatures.Monoid][] module of the [Agda Universal Algebra Library][].

A monoid's signature expands the magma signature by a single *nullary* operation
symbol `ε-Op` denoting the identity element.  This is the first signature in the
[`Classical/`][Classical] tree that genuinely grows — `Semigroup` reused
`Sig-Magma` — so it is the first place the forgetful projection is a reduct rather
than `proj₁`.  Distinguished elements are nullary operation symbols of the
signature per [ADR-002 v2 §9](../../docs/adr/002-classical-layer-design.md);
`ε-Op` has arity `Fin 0`.  The constructor- and arity-naming conventions are those
established by `Classical.Signatures.Magma`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Signatures.Monoid where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive using () renaming ( Set to Type )
open import Data.Fin.Base  using ( Fin )
open import Data.Product   using ( _,_ )
open import Level          using ( 0ℓ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Signatures using ( Signature )

data Op-Monoid : Type where
  ∙-Op ε-Op : Op-Monoid

ar-Monoid : Op-Monoid → Type
ar-Monoid ∙-Op = Fin 2
ar-Monoid ε-Op = Fin 0

Sig-Monoid : Signature 0ℓ 0ℓ
Sig-Monoid = Op-Monoid , ar-Monoid
```

--------------------------------------

<span style="float:left;">[← Classical.Signatures.Magma](Classical.Signatures.Magma.html)</span>
<span style="float:right;">[Classical.Signatures.Group →](Classical.Signatures.Group.html)</span>

{% include UALib.Links.md %}
