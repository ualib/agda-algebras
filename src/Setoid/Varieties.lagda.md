---
layout: default
title : "Setoid.Varieties module (Agda Universal Algebra Library)"
date : "2021-07-26"
author: "agda-algebras development team"
---

### Equations and Varieties for Setoids

This is the [Setoid.Varieties][] module of the [Agda Universal Algebra Library][].

A **variety** is a class of `𝑆`-algebras closed under homomorphic images,
subalgebras and arbitrary products.  Writing `H`, `S` and `P` for those three
closure operators and `V` for the composite `H ∘ S ∘ P`, a class `𝒦` is a variety
exactly when `V 𝒦 ⊆ 𝒦`.  Birkhoff's HSP theorem identifies the varieties with the
*equationally definable* classes, and proving it constructively is what this
subtree exists for.

This is a barrel module: it declares nothing of its own and re-exports the
following:

+  [Setoid.Varieties.Closure][]: the operators `H`, `S`, `P` and `V` themselves;
+  [Setoid.Varieties.EquationalLogic][] and [Setoid.Varieties.Interpretation][]:
   equations, the satisfaction relation, and `Mod`{.AgdaFunction} and
   `Th`{.AgdaFunction};
+  [Setoid.Varieties.SoundAndComplete][]: the derivation rules of equational
   logic, with soundness and Birkhoff's completeness theorem;
+  [Setoid.Varieties.Preservation][] and [Setoid.Varieties.Invariance][]: that
   each closure operator preserves identities, and that satisfaction is invariant
   under the algebraic constructions;
+  [Setoid.Varieties.FreeAlgebras][] and [Setoid.Varieties.FreeSubstitution][]:
   the relatively free algebra of a class;
+  [Setoid.Varieties.HSP][]: Birkhoff's variety theorem;
+  [Setoid.Varieties.Maltsev][]: Maltsev conditions, the equational
   characterisations of congruence-lattice properties;
+  [Setoid.Varieties.Invariants][], [Setoid.Varieties.Properties][] and
   [Setoid.Varieties.Reducts][]: the remaining supporting results.


```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Varieties where

open import Setoid.Varieties.Closure  public
open import Setoid.Varieties.EquationalLogic  public
open import Setoid.Varieties.FreeAlgebras  public
open import Setoid.Varieties.FreeSubstitution  public
open import Setoid.Varieties.HSP  public
open import Setoid.Varieties.Interpretation             public
open import Setoid.Varieties.Invariance                 public
open import Setoid.Varieties.Invariants  public
open import Setoid.Varieties.Maltsev                    public
open import Setoid.Varieties.Preservation  public
open import Setoid.Varieties.Properties  public
open import Setoid.Varieties.Reducts                    public
open import Setoid.Varieties.SoundAndComplete  public
```
