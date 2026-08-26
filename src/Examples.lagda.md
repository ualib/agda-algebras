---
layout: default
title : "Examples module"
date : "2022-18-06"
author: "the agda-algebras development team"
---

### Examples

This is the [Examples][] module of the [Agda Universal Algebra Library][].

This is the aggregator for the example tree: importing it type-checks every worked
example in the library.  The submodules group the examples by flavour, as follows:

+  [Examples.Classical][] pairs one worked instance with each classical structure:
   canonical first examples, finite groups from Cayley tables, the two-element
   lattices, and deliberate failure modes such as a magma that is not a semigroup.
+  [Examples.Demos][] collects self-contained demonstrations, among them the
   frozen literate artifact of the TYPES 2021 paper.
+  [Examples.FunctionTypeBijections][] and [Examples.PolynomialFunctors][] are
   illustrative studies relocated out of the Legacy tree: n-ary function encodings
   and their η-obstructions, and polynomial functors with W-types.
+  [Examples.Setoid][] exercises the generic `Setoid/` machinery directly: free
   algebras, presentations, quotients, and Birkhoff's HSP theorem specialized to a
   concrete algebra.
+  [Examples.Structures][] instantiates the general operations-and-relations
   structures of the frozen Legacy tree.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples where

open import Examples.Classical
open import Examples.Demos
open import Examples.FunctionTypeBijections
open import Examples.PolynomialFunctors
open import Examples.Setoid
open import Examples.Structures
```
