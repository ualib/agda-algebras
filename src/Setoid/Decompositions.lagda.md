---
layout: default
file: "src/Setoid/Decompositions.lagda.md"
title: "Setoid.Decompositions module (The Agda Universal Algebra Library)"
date: "2026-10-13"
author: "the agda-algebras development team"
---

### Direct decompositions

This is the [Setoid.Decompositions][] module of the [Agda Universal Algebra Library][].

A **direct decomposition** of an algebra `𝑨` is an isomorphism `𝑨 ≅ ∏ᵢ 𝑩ᵢ` with a
product of algebras.  Where a subdirect decomposition
([Setoid.Subalgebras.Subdirect][]) embeds `𝑨` in a product, a direct one
identifies `𝑨` with all of it.  The factors of such an isomorphism are quotients
of `𝑨`, so a direct decomposition is determined by a family of congruences of
`𝑨`, and the theory runs inside the congruence lattice: the meet of the family is
the diagonal, as for a subdirect decomposition, and moreover every tuple of
elements is interpolated.  The algebras that admit no proper direct decomposition
are the directly indecomposable ones, and an algebra is *uniquely factorable* when
it is a product of directly indecomposable algebras in only one way.

The development follows McKenzie, McNulty, and Taylor, *Algebras, Lattices,
Varieties* I, §4.4 and Chapter 5, and quotes each definition and theorem it
formalizes by number.  This is a barrel module, re-exporting the following:

+  [Setoid.Decompositions.FactorPairs][]: factor pairs of congruences
   (Definition 4.28), the binary product of congruences of §5.2, the isomorphism
   `𝑨 ≅ 𝑨/θ × 𝑨/φ` of Theorem 4.29 and its converse, and the decidability of
   factor congruences;
+  [Setoid.Decompositions.Products][]: products of arbitrary families of
   congruences (Definition 4.30 and Lemmas 1 and 3 of §5.2) and the direct
   representations of Theorem 4.31;
+  [Setoid.Decompositions.Indecomposable][]: directly indecomposable algebras
   (Definition 4.37), indecomposable congruences and Lemma 2 of §5.2, and
   invariance under isomorphism;
+  [Setoid.Decompositions.Finite][]: decision procedures for finite algebras,
   the list of all factor pairs, the theorem that an algebra of at most three
   elements is directly indecomposable, and the factorization of every finite
   algebra into directly indecomposable ones (Exercise 4.38 (2));
+  [Setoid.Decompositions.StrictRefinement][]: the strict refinement property
   (§5.6), Theorem 5.16 on decompositions into indecomposables, and the theorem
   that a finite algebra with the strict refinement property is uniquely
   factorable.

The worked example is the cyclic group of order six, `ℤ₆ ≅ ℤ₂ × ℤ₃`, in
[Examples.Classical.Groups.CyclicGroup6][].

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Setoid.Decompositions where

open import Setoid.Decompositions.FactorPairs       public
open import Setoid.Decompositions.Finite            public
open import Setoid.Decompositions.Indecomposable    public
open import Setoid.Decompositions.Products          public
open import Setoid.Decompositions.StrictRefinement  public
```
