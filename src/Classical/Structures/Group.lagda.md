---
layout: default
file: "src/Classical/Structures/Group.lagda.md"
title: "Classical.Structures.Group module"
date: "2026-05-30"
author: "the agda-algebras development team"
---

### Groups {#classical-structures-group}

This is the [Classical.Structures.Group][] module of the [Agda Universal Algebra Library][].

This is a barrel module: it declares nothing of its own and re-exports the nineteen
modules that develop group theory in the `Classical/` tree.  A group here is an
algebra over `Sig-Group`{.AgdaFunction} satisfying `Th-Group`{.AgdaFunction}, so it
is a group in the universal-algebraic sense: three operations and five equations,
with no appeal to the standard library's bundles except through the bridge of
[Classical.Bundles.Group][].

This is much the largest structure tree in `Classical/`, because it is the one the
FLRP research track is built on, so a thematic map is more use than a list:

+  **The structures.** [Classical.Structures.Group.Basic][] for
   `Group`{.AgdaFunction} and the named accessors;
   [Classical.Structures.Group.AbelianGroup][] for the commutative case.
+  **Subgroups.** [Classical.Structures.Group.Subgroups][] and
   [Classical.Structures.Group.SubgroupLattice][] for subgroups and their lattice;
   [Classical.Structures.Group.PartitionSubgroup][] for the partition subgroups of a
   finite power; [Classical.Structures.Group.Complements][] for permuting
   complements in an interval of that lattice;
   [Classical.Structures.Group.Dedekind][] for Dedekind's rule.
+  **Normality.** [Classical.Structures.Group.Conjugation][] and
   [Classical.Structures.Group.Congruences][] relate normal subgroups to
   congruences; [Classical.Structures.Group.NormalSubgroupLattice][] is their
   lattice; [Classical.Structures.Group.NormalCore][] is the largest normal subgroup
   inside a given one; [Classical.Structures.Group.MinimalNormal][] covers minimal
   normal subgroups and monoliths; [Classical.Structures.Group.Centralizer][] covers
   centralizers.
+  **Cosets and actions.** [Classical.Structures.Group.Cosets][] for `G/H` as a
   setoid; [Classical.Structures.Group.GSet][] for the same space as a unary algebra,
   which is how a group action is represented here.
+  **Constructions.** [Classical.Structures.Group.Product][] and
   [Classical.Structures.Group.Power][] for binary and indexed products;
   [Classical.Structures.Group.Diagonal][] for the diagonal subgroup of a power;
   [Classical.Structures.Group.Complexes][] for complex products.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group where

open import Classical.Structures.Group.Basic public
open import Classical.Structures.Group.Centralizer public
open import Classical.Structures.Group.AbelianGroup public
open import Classical.Structures.Group.Complements public
open import Classical.Structures.Group.Complexes public
open import Classical.Structures.Group.Congruences public
open import Classical.Structures.Group.Conjugation public
open import Classical.Structures.Group.Cosets public
open import Classical.Structures.Group.Dedekind public
open import Classical.Structures.Group.Diagonal public
open import Classical.Structures.Group.GSet public
open import Classical.Structures.Group.MinimalNormal public
open import Classical.Structures.Group.NormalCore public
open import Classical.Structures.Group.NormalSubgroupLattice public
open import Classical.Structures.Group.PartitionSubgroup public
open import Classical.Structures.Group.Power public
open import Classical.Structures.Group.Product public
open import Classical.Structures.Group.Subgroups public
open import Classical.Structures.Group.SubgroupLattice public
```
