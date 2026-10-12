---
layout: default
file: "src/Classical/Structures/Lattice/Free/Canonical.lagda.md"
title: "Classical.Structures.Lattice.Free.Canonical module"
date: "2026-10-11"
author: "the agda-algebras development team"
---

### Canonical forms in free lattices

This is the [Classical.Structures.Lattice.Free.Canonical][] module of the [Agda Universal Algebra Library][].

Whitman's procedure decides whether two lattice terms name the same element of the
free lattice `FL(X)`; it does not choose a name.  Every element of a free lattice
has a term of minimal rank representing it, unique up to commutativity, its
*canonical form* ([Freese, Ježek, and Nation (1995)][], Theorem 1.17), and Theorem
1.18 characterizes that form by four syntactic conditions.  This is a barrel
module: it declares nothing of its own and re-exports the four modules that
formalize canonical forms.

### Guide to the submodules of <span class="AgdaModule">Classical.Structures.Lattice.Free.Canonical</span>

+  [Classical.Structures.Lattice.Free.Canonical.Basic][]: the canonical terms
   `CTerm X`{.AgdaDatatype}, with joins and meets of lists of children, their
   embedding `⌊_⌋`{.AgdaFunction} into lattice terms, their rank, the predicate
   `IsCanonical`{.AgdaDatatype} stating the four conditions of Theorem 1.18, and
   the duality that exchanges joins and meets;
+  [Classical.Structures.Lattice.Free.Canonical.Algorithm][]: the function
   `canonical`{.AgdaFunction} that computes the canonical form of a lattice term,
   a well-founded recursion on rank, with the theorems that the result represents
   the term and is canonical;
+  [Classical.Structures.Lattice.Free.Canonical.Uniqueness][]: equality up to
   commutativity `_≈ᶜ_`{.AgdaDatatype}, Lemma 1.16, Theorem 1.17 (two canonical
   terms representing the same element are related), and the decision of equality
   in the free lattice by comparison of canonical forms;
+  [Classical.Structures.Lattice.Free.Canonical.Joinands][]: the canonical joinands
   and meetands of an element and Theorem 1.19, their refinement of every join (and
   meet) representation.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Classical.Structures.Lattice.Free.Canonical where

open import Classical.Structures.Lattice.Free.Canonical.Algorithm   public
open import Classical.Structures.Lattice.Free.Canonical.Basic       public
open import Classical.Structures.Lattice.Free.Canonical.Joinands    public
open import Classical.Structures.Lattice.Free.Canonical.Uniqueness  public
```
