---
layout: default
file: "src/Classical/Signatures/Lattice.lagda.md"
title: "Classical.Signatures.Lattice module"
date: "2026-05-27"
author: "the agda-algebras development team"
---

### The signature of lattices

This is the [Classical.Signatures.Lattice][] module of the [Agda Universal Algebra Library][].

A lattice's signature has two binary operation symbols, `∧-Op` (meet) and `∨-Op`
(join), both of arity `Fin 2`.  This is the first signature in the
[`Classical/`][Classical] tree with *two distinct binary symbols* and the first
that does not extend `Sig-Magma` or `Sig-Monoid` by a single symbol — it stands
alone, parallel to them rather than over them.  The decision to carry both symbols
in the signature, rather than treating one as the primitive and the other as
derived, is recorded in
[ADR-002 v2 §5, §9](../../docs/adr/002-classical-layer-design.md): each operation
that participates in the variety's equations gets its own signature symbol.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Signatures.Lattice where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive using () renaming ( Set to Type )
open import Data.Fin.Base  using ( Fin )
open import Data.Product   using ( _,_ )
open import Level          using ( 0ℓ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Signatures using ( Signature )
```
-->

```agda
data Op-Lattice : Type where
  ∧-Op ∨-Op : Op-Lattice

ar-Lattice : Op-Lattice → Type
ar-Lattice ∧-Op = Fin 2
ar-Lattice ∨-Op = Fin 2

Sig-Lattice : Signature 0ℓ 0ℓ
Sig-Lattice = Op-Lattice , ar-Lattice
```
