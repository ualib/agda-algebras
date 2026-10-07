---
layout: default
file: "src/Classical/Structures/Lattice/Free.lagda.md"
title: "Classical.Structures.Lattice.Free module"
date: "2026-10-07"
author: "the agda-algebras development team"
---

### Free lattices

This is the [Classical.Structures.Lattice.Free][] module of the [Agda Universal Algebra Library][].

This is a barrel module: it declares nothing of its own and re-exports the modules
that construct the free lattice `FL(X)` and decide its order by Whitman's solution
to the word problem ([Freese, Ježek, and Nation (1995)][], Chapter I).  The
development is syntactic: `FL(X)` is the set of lattice terms ordered by the
relation Whitman's rules define, and the rules are proved sound and complete for
the order of every lattice, rather than read off a model built by Day's doubling
construction as in the book.

### Guide to the submodules of <span class="AgdaModule">Classical.Structures.Lattice.Free</span>

+  [Classical.Structures.Lattice.Free.Term][]: the lattice terms
   `LatTerm X`{.AgdaDatatype}, their rank, their evaluation in any lattice, and
   the translation to and from the generic `Term X`{.AgdaDatatype} over
   `Sig-Lattice`{.AgdaFunction};
+  [Classical.Structures.Lattice.Free.Whitman][]: Whitman's rules as the inductive
   relation `_≤ʷ_`{.AgdaDatatype}, its decision procedure, reflexivity,
   transitivity, and formal meet and join as infimum and supremum;
+  [Classical.Structures.Lattice.Free.Universal][]: the free lattice
   `FL X`{.AgdaFunction}, soundness and completeness of the rules (Whitman's
   theorem), and the universal property;
+  [Classical.Structures.Lattice.Free.Derivability][]: the bridge to equational
   logic, which makes derivable equality under `Th-Lattice`{.AgdaFunction}, and
   hence equality in the relatively free algebra `𝔽[ X ]`{.AgdaFunction},
   decidable.

The worked example [Examples.Classical.Lattices.FreeLattice3][] decides a few
inequalities in `FL(3)` by evaluation.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Classical.Structures.Lattice.Free where

open import Classical.Structures.Lattice.Free.Derivability  public
open import Classical.Structures.Lattice.Free.Term          public
open import Classical.Structures.Lattice.Free.Universal     public
open import Classical.Structures.Lattice.Free.Whitman       public
```
