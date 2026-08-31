---
layout: default
file: "src/Classical/Structures/Group.lagda.md"
title: "Classical.Structures.Group module"
date: "2026-05-30"
author: "the agda-algebras development team"
---

### Groups {#classical-structures-group}

This is the [Classical.Structures.Group][] module of the [Agda Universal Algebra Library][].

This is a barrel module: it declares nothing of its own and re-exports the
modules that develop group theory in the `Classical/` tree.

A group here is an algebra over `Sig-Group`{.AgdaFunction} satisfying
`Th-Group`{.AgdaFunction}, so it is a group in the universal-algebraic sense:
three operations and five equations, with no appeal to the standard library's
bundles except through the bridge of [Classical.Bundles.Group][].

#### Guide to the submodules of <span class="AgdaModule">Classical.Structures.Group</span>

This is currently the largest structure tree in `Classical/`, because it is the
one the FLRP research track is built on, so a thematic map is of more use than a
list.

+  **Structures**.

   +  [Classical.Structures.Group.Basic][]:
      `Group`{.AgdaFunction} and the named accessors;
   +  [Classical.Structures.Group.AbelianGroup][]: commutative groups.

+  **Subgroups**.

   +  [Classical.Structures.Group.Subgroups][],
      [Classical.Structures.Group.SubgroupLattice][]:
      subgroups and their lattice;
   +  [Classical.Structures.Group.PartitionSubgroup][]:
      partition subgroups of a finite power;
   +  [Classical.Structures.Group.Complements][]:
      permuting complements in an interval of a subgroup lattice;
   +  [Classical.Structures.Group.Dedekind][]: Dedekind's rule.

+  **Normality**.

   +  [Classical.Structures.Group.Conjugation][],
      [Classical.Structures.Group.Congruences][]:
      normal subgroups and congruences;
   +  [Classical.Structures.Group.NormalSubgroupLattice][]:
      congruence lattices of groups;
   +  [Classical.Structures.Group.NormalCore][]:
      maximal normal subgroups;
   +  [Classical.Structures.Group.MinimalNormal][]:
      minimal normal subgroups and monoliths;
   +  [Classical.Structures.Group.MaximalSubgroup][]:
      maximal subgroups, as the classification data the two-element-chain
      catalog entry consumes;
   +  [Classical.Structures.Group.Centralizer][]: centralizers.

+  **Cosets and group actions**.

   +  [Classical.Structures.Group.Cosets][]:
      `G/H` as a setoid;
   +  [Classical.Structures.Group.GSet][]:
      group-action unary algebras.

+  **Constructions**.

   +  [Classical.Structures.Group.Product][],
      [Classical.Structures.Group.Power][]:
      binary and indexed products;

   +  [Classical.Structures.Group.Diagonal][]:
      the diagonal subgroup of a power;

   +  [Classical.Structures.Group.Complexes][]:
      complex products.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group where

open import Classical.Structures.Group.Basic                  public

open import Classical.Structures.Group.AbelianGroup           public
open import Classical.Structures.Group.Centralizer            public
open import Classical.Structures.Group.Complements            public
open import Classical.Structures.Group.Complexes              public
open import Classical.Structures.Group.Congruences            public
open import Classical.Structures.Group.Conjugation            public
open import Classical.Structures.Group.Cosets                 public
open import Classical.Structures.Group.Dedekind               public
open import Classical.Structures.Group.Diagonal               public
open import Classical.Structures.Group.GSet                   public
open import Classical.Structures.Group.IndexAction            public
open import Classical.Structures.Group.MaximalSubgroup        public
open import Classical.Structures.Group.MinimalNormal          public
open import Classical.Structures.Group.NormalCore             public
open import Classical.Structures.Group.NormalSubgroupLattice  public
open import Classical.Structures.Group.PartitionSubgroup      public
open import Classical.Structures.Group.Power                  public
open import Classical.Structures.Group.Product                public
open import Classical.Structures.Group.SubgroupLattice        public
open import Classical.Structures.Group.Subgroups              public
open import Classical.Structures.Group.Wreath                 public
```
