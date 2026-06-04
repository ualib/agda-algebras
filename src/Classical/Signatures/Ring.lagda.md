---
layout: default
file: "src/Classical/Signatures/Ring.lagda.md"
title: "Classical.Signatures.Ring module"
date: "2026-05-30"
author: "the agda-algebras development team"
---

### The signature of rings

This is the [Classical.Signatures.Ring][] module of the [Agda Universal Algebra Library][].

A ring's signature carries five operation symbols: the additive binary `+-Op`, the
additive identity `0-Op` (nullary), the additive inverse `-Op` (unary), the
multiplicative binary `·-Op`, and the multiplicative identity `1-Op` (nullary).  It
is the first signature in the [`Classical/`][Classical] tree to carry *two* binary
symbols *and* distinguished elements *and* a unary symbol — the additive triple
`(+-Op, 0-Op, -Op)` is an abelian-group signature, the multiplicative pair
`(·-Op, 1-Op)` is a monoid signature, and the two are tied together by the
distributivity equations in `Th-Ring`.  Per
[ADR-002 v2 §5, §9](../../docs/adr/002-classical-layer-design.md), every operation
that participates in the variety's equations gets its own signature symbol; the
constructor- and arity-naming conventions are those established by
`Classical.Signatures.Magma` and its successors.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Signatures.Ring where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive using () renaming ( Set to Type )
open import Data.Fin.Base  using ( Fin )
open import Data.Product   using ( _,_ )
open import Level          using ( 0ℓ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Signatures using ( Signature )

data Op-Ring : Type where
  +-Op 0-Op -Op ·-Op 1-Op : Op-Ring

ar-Ring : Op-Ring → Type
ar-Ring +-Op = Fin 2
ar-Ring 0-Op = Fin 0
ar-Ring -Op  = Fin 1
ar-Ring ·-Op = Fin 2
ar-Ring 1-Op = Fin 0

Sig-Ring : Signature 0ℓ 0ℓ
Sig-Ring = Op-Ring , ar-Ring
```

--------------------------------------

<span style="float:left;">[← Classical.Signatures.Group](Classical.Signatures.Group.html)</span>

{% include UALib.Links.md %}
