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
   decidable;
+  [Classical.Structures.Lattice.Free.Duality][]: the involution of lattice terms
   that exchanges meet and join and reverses Whitman's order;
+  [Classical.Structures.Lattice.Free.Canonical][]: canonical forms (Theorems 1.17
   and 1.18), the algorithm that computes them, their uniqueness up to
   commutativity, and the canonical joinands of an element (Theorem 1.19);
+  [Classical.Structures.Lattice.Free.Semidistributive][]: free lattices satisfy
   Whitman's condition (Theorem 1.8) and are semidistributive (Theorem 1.21);
+  [Classical.Structures.Lattice.Free.Substitution][]: substitutions, the
   homomorphisms `FL(X) → FL(Y)` they induce, the evaluation lemma, and the
   theorem that every such homomorphism is induced by a substitution;
+  [Classical.Structures.Lattice.Free.Closure][]: the kernel of a substitution,
   solutions of a list of equations, and the closure of McNulty's free-lattice
   Nullstellensatz problem, with refutation certificates;
+  [Classical.Structures.Lattice.Free.Generation][]: free generating sets
   (Corollaries 1.12 and 1.13, with Lemma 1.3), their decision procedure, and the
   irreducibility of free generators (Corollary 1.6);
+  [Classical.Structures.Lattice.Free.Embedding][]: Lemma 9.13 (an embedding of
   free lattices sends a canonical joinand that is not a generator to a canonical
   joinand), its dual, and the one-step truncation property.

The worked example [Examples.Classical.Lattices.FreeLattice3][] decides a few
inequalities in `FL(3)` by evaluation and computes some canonical forms.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Classical.Structures.Lattice.Free where

open import Classical.Structures.Lattice.Free.Canonical         public
open import Classical.Structures.Lattice.Free.Closure           public
open import Classical.Structures.Lattice.Free.Derivability      public
open import Classical.Structures.Lattice.Free.Duality           public
open import Classical.Structures.Lattice.Free.Embedding         public
open import Classical.Structures.Lattice.Free.Generation        public
open import Classical.Structures.Lattice.Free.Semidistributive  public
open import Classical.Structures.Lattice.Free.Substitution      public
open import Classical.Structures.Lattice.Free.Term              public
open import Classical.Structures.Lattice.Free.Universal         public
open import Classical.Structures.Lattice.Free.Whitman           public
```
