---
layout: default
title : "Setoid.Algebras module (Agda Universal Algebra Library)"
date : "2021-09-17"
author: "agda-algebras development team"
---

### Setoid Representation of Algebras

This is the [Setoid.Algebras][] module of the [Agda Universal Algebra Library][].

This is a barrel module: it declares nothing of its own and re-exports the four
modules that define algebras over setoids.  An algebra here is a setoid together
with an interpretation of every operation symbol as a setoid function on it, so
that each operation respects the carrier's equivalence; [ADR-001][] records why
that, rather than a bare type under propositional equality, is the canonical
representation.

#### Submodule guide

+  [Setoid.Algebras.Basic][]: the `Algebra`{.AgdaRecord} record, the smart
   constructors `mkAlgebra`{.AgdaFunction} and `mkAlgebraₚ`{.AgdaFunction}, the
   interpretation operator `_^_`{.AgdaFunction}, the domain and carrier projections
   `𝔻[_]`{.AgdaFunction} and `𝕌[_]`{.AgdaFunction}, and universe lifting;
+  [Setoid.Algebras.Products][]: products of indexed families and of classes;
+  [Setoid.Algebras.Finite][]: the `FiniteAlgebra`{.AgdaRecord} interface;
+  [Setoid.Algebras.Reduct][]: reducts along a signature morphism, and their functoriality.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Algebras where

open import Setoid.Algebras.Basic     public
open import Setoid.Algebras.Finite    public
open import Setoid.Algebras.Products  public
open import Setoid.Algebras.Reduct    public
```
