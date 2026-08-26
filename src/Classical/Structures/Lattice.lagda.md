---
layout: default
file: "src/Classical/Structures/Lattice.lagda.md"
title: "Classical.Structures.Lattice module"
date: "2026-07-25"
author: "the agda-algebras development team"
---

### Lattices {#classical-structures-lattices}

This is the [Classical.Structures.Lattice][] module of the [Agda Universal Algebra Library][].

This is a barrel module: it declares nothing of its own and re-exports the seven
modules that develop lattices in the `Classical/` tree.  A lattice here is an
algebra over `Sig-Lattice`{.AgdaFunction} satisfying `Th-Lattice`{.AgdaFunction},
that is, the *equational* presentation; the order-theoretic presentation, in which
meet and join are recovered as the infimum and supremum of a partial order, is what
[Setoid.Subalgebras.CompleteLattice][] and [Setoid.Congruences.CompleteLattice][]
build instead.

### Guide to the submodules of <span class="AgdaModule">Classical.Structures.Lattice</span>

+  [Classical.Structures.Lattice.Basic][]: the type `Lattice`{.AgdaFunction}
   itself, the two magma reducts, and the named accessors;
+  [Classical.Structures.Lattice.DistributiveLattice][]: the same signature with
   distributivity added to the theory;
+  [Classical.Structures.Lattice.Dual][]: meet and join exchanged.  Since
   `Th-Lattice`{.AgdaFunction} is self-dual the construction needs no new equations.
   Dualizing twice recovers each operation *pointwise*, but the involution is not
   formalized there, because stating it as an equality of `Lattice`{.AgdaFunction}
   values would need function extensionality and no consumer has required it;
+  [Classical.Structures.Lattice.Product][]: the direct product of two lattices,
   coordinatewise;
+  [Classical.Structures.Lattice.OrdinalSum][]: one lattice stacked on another with
   the top of the lower glued to the bottom of the upper, written `L ⊕ₐ M` in the
   small-lattice-representations manuscript;
+  [Classical.Structures.Lattice.Parachute][]: a fresh bottom element beneath `n`
   side-by-side canopies, the construction the FLRP work is built on;
+  [Classical.Structures.Lattice.Partitions][]: the partition lattice
   `Eq(n)`{.AgdaFunction}, the equivalence relations on an `n`-element set ordered
   by refinement.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Lattice where

open import Classical.Structures.Lattice.Basic                public
open import Classical.Structures.Lattice.DistributiveLattice  public
open import Classical.Structures.Lattice.Dual                 public
open import Classical.Structures.Lattice.OrdinalSum           public
open import Classical.Structures.Lattice.Parachute            public
open import Classical.Structures.Lattice.Partitions           public
open import Classical.Structures.Lattice.Product              public

```
