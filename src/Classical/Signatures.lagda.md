---
layout: default
file: "src/Classical/Signatures.lagda.md"
title: "Classical.Signatures module"
date: "2026-05-15"
author: "the agda-algebras development team"
---

### Signatures of classical structures

This is the [Classical.Signatures][] module of the [Agda Universal Algebra Library][].

The `Classical/Signatures/` subtree houses the per-structure signature definitions
for the classical-structures tree.  Each concrete structure `X` carries a fixed
signature `𝑆ₓ : Signature 𝓞 𝓥` whose sort `Op` enumerates the operation symbols of
`X` together with their arities, defined in a module
`Classical/Signatures/X.lagda.md` and re-exported from this umbrella.  The design
rationale — Σ-typed cores over signature-equation pairs, with record-typed bundle
views for stdlib interop — is recorded in [ADR-002][ADR-002].

This file is the umbrella for the subtree.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Signatures where

open import Classical.Signatures.Finite public
open import Classical.Signatures.Group public
open import Classical.Signatures.Lattice public
open import Classical.Signatures.Magma public
open import Classical.Signatures.Monoid public
open import Classical.Signatures.Ring public
open import Classical.Signatures.Unary public
```
