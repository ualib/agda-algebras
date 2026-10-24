---
layout: default
file: "src/Classical/Structures/Lattice.lagda.md"
title: "Classical.Structures.Lattice module"
date: "2026-07-25"
author: "the agda-algebras development team"
---

### Lattices {#classical-structures-lattices}

This is the [Classical.Structures.Lattice][] module of the [Agda Universal Algebra Library][].

This is a barrel module: it declares nothing of its own and re-exports the two
modules that develop lattices in the `Classical/` tree.  A lattice here is an
algebra over `Sig-Lattice`{.AgdaFunction} satisfying `Th-Lattice`{.AgdaFunction},
that is, the *equational* presentation; the order-theoretic presentation, in which
meet and join are recovered as the infimum and supremum of a partial order, is what
[Setoid.Subalgebras.CompleteLattice][] and [Setoid.Congruences.CompleteLattice][]
build instead.

### Guide to the submodules of <span class="AgdaModule">Classical.Structures.Lattice</span>

+  [Classical.Structures.Lattice.Basic][]: the type `Lattice`{.AgdaFunction}
   itself, the two magma reducts, and the named accessors;
+  [Classical.Structures.Lattice.Partitions][]: the partition lattice
   `Eq(n)`{.AgdaFunction}, the equivalence relations on an `n`-element set ordered
   by refinement.

The rest of lattice theory, which this barrel re-exported until October 2026,
continues in the library ualib/agda-lattices, which builds on this one: the
free lattice `FL(X)`, with Whitman's solution to its word problem and its
canonical forms, the finite lattices built from operation tables, distributive
lattices, the dual of a lattice, principal filters and ideals, binary
products, and ordinal sums.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Classical.Structures.Lattice where

open import Classical.Structures.Lattice.Basic       public
open import Classical.Structures.Lattice.Partitions  public

```
