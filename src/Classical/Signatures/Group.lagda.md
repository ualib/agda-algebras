---
layout: default
file: "src/Classical/Signatures/Group.lagda.md"
title: "Classical.Signatures.Group module"
date: "2026-05-30"
author: "the agda-algebras development team"
---

### <a id="classical-signatures-group">The signature of groups</a>

This is the [Classical.Signatures.Group][] module of the [Agda Universal Algebra Library][].

A group's signature expands the monoid signature by a single *unary* operation
symbol `⁻¹-Op` denoting the inverse.  It is the first signature in the
[`Classical/`][Classical] tree to carry an operation of every arity below three —
binary `∙-Op`, nullary `ε-Op`, unary `⁻¹-Op` — and so the first whose forgetful
projection to its predecessor (`group→monoid`) drops a *unary* symbol rather than a
nullary one.  Distinguished elements and inverses alike are operation symbols of the
signature per [ADR-002 v2 §9](../../docs/adr/002-classical-layer-design.md); `⁻¹-Op`
has arity `Fin 1`.  The constructor- and arity-naming conventions are those
established by `Classical.Signatures.Magma` and extended by
`Classical.Signatures.Monoid`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Signatures.Group where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive using () renaming ( Set to Type )
open import Data.Fin.Base  using ( Fin )
open import Data.Product   using ( _,_ )
open import Level          using ( 0ℓ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Signatures using ( Signature )

data Op-Group : Type where
  ∙-Op ε-Op ⁻¹-Op : Op-Group

ar-Group : Op-Group → Type
ar-Group ∙-Op  = Fin 2
ar-Group ε-Op  = Fin 0
ar-Group ⁻¹-Op = Fin 1

Sig-Group : Signature 0ℓ 0ℓ
Sig-Group = Op-Group , ar-Group
```

--------------------------------------

<span style="float:left;">[← Classical.Signatures.Monoid](Classical.Signatures.Monoid.html)</span>
<span style="float:right;">[Classical.Signatures.Ring →](Classical.Signatures.Ring.html)</span>

{% include UALib.Links.md %}
