---
layout: default
title : "Overture module"
date : "2022-17-06"
author: "the agda-algebras development team"
---

## Overture

This is the [Overture][] module of the [Agda Universal Algebra Library][].

The Overture is the foundation layer: the vocabulary every later tree (`Setoid/`,
`Classical/`, `FLRP/`) imports.  In re-export order:

+  [Overture.Preface][] is the front door: why the library exists, why Agda, and
   how to read what follows.
+  [Overture.Basic][] sets the logical foundations and shared preliminaries.
+  [Overture.Signatures][] defines the `Signature` type: operation symbols paired
   with an arity function.
+  [Overture.Operations][] represents an operation of arity `I` as a function
   from tuples `I → A` to `A`.
+  [Overture.Relations][] supplies the relation vocabulary, including the
   `Equivalence` bundle over a fixed carrier.
+  [Overture.Functions][] collects the raw-function infrastructure (images,
   computed inverses, surjectivity) that the `Setoid/` tree builds on.
+  [Overture.Terms][] gives terms over a signature, their interpretation, and
   translation along signature morphisms.
+  [Overture.Adjunction][] is the order-theoretic adjunction toolkit: closure,
   Galois connections, residuation.
+  [Overture.Cayley][] represents finite binary operations by Cayley tables, with
   decision procedures that discharge their laws.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Overture where

open import Overture.Preface     public
open import Overture.Basic       public
open import Overture.Signatures  public
open import Overture.Operations  public
open import Overture.Relations   public
open import Overture.Functions   public
open import Overture.Terms       public
open import Overture.Adjunction  public
open import Overture.Cayley      public
```
