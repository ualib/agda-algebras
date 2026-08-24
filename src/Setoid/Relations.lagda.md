---
layout: default
title : "Setoid.Relations module (The Agda Universal Algebra Library)"
date : "2021-09-17"
author: "the agda-algebras development team"
---

## Relations on setoids

This is the [Setoid.Relations][] module of the [Agda Universal Algebra Library][].

This is a barrel module: it declares nothing of its own and re-exports the four
modules on relations over setoids.  The distinction this tree turns on is between
a relation on a setoid's *carrier* and one that respects the setoid's equality.
Both are wanted, and neither subsumes the other, so the relation types take bare
carriers and "respects the equality" is stated separately as needed.  A congruence,
for instance, is required to contain the setoid equality exactly so that
quotienting by it is well defined.

### Guide to the submodules of <span class="AgdaModule">Setoid.Relations</span>

+  [Setoid.Relations.Discrete][]: binary relations, pointwise equality of setoid
   functions, image containment, and the kernel of a setoid function;
+  [Setoid.Relations.Quotients][]: equivalence classes, the quotient setoid
   `_/_`{.AgdaFunction}, and that a kernel is an equivalence relation;
+  [Setoid.Relations.Continuous][]: relations of arbitrary arity, where the arity
   is an arbitrary type rather than a natural number, so that finite, countable
   and uncountable arities are handled uniformly;
+  [Setoid.Relations.Properties][]: no results of its own, but a public
   re-export of the standard library's `Relation.Binary.Definitions`, so that
   `Reflexive`{.AgdaFunction}, `Symmetric`{.AgdaFunction},
   `Transitive`{.AgdaFunction} and their companions are in scope for anything
   that opens the barrel.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Relations where

open import Setoid.Relations.Discrete    public
open import Setoid.Relations.Quotients   public
open import Setoid.Relations.Continuous  public
open import Setoid.Relations.Properties  public
```
