---
layout: default
file: "src/FLRP/KurzweilNetter.lagda.md"
title: "FLRP.KurzweilNetter module (The Agda Universal Algebra Library)"
date: "2026-07-28"
author: "the agda-algebras development team"
---

### The Kurzweil–Netter theorem

This is the [FLRP.KurzweilNetter][] module of the [Agda Universal Algebra Library][].

**Theorem.**  The class of decidably representable lattices is closed under the taking of lattice duals.

Hans Kurzweil (1985) proved the group-side result, representing duals on intervals in subgroup lattices; his student Raimund Netter (1986) generalized it to congruence lattices of arbitrary finite algebras, which is the statement proved here.  This directory holds everything specific to the theorem: the statement of Kurzweil's interval lemma and its proof, the algebra-side reduction, the composite proof, and the closed instantiation.  What is *not* here is deliberate: the reusable group theory lives under `Classical.Structures.Group` ([Classical.Structures.Group.PartitionSubgroup][], [Classical.Structures.Group.PowerCollapse][], [Classical.Structures.Group.Commutator][]), and the registry entries the theorem retired (Entries 2 and 4) live in [FLRP.Assumptions][].

#### How the proof is organized

Given a decidable representation `𝑳 ≅ DecCon 𝑨`, the dual is represented on the coset space `Sᵐ/D` of a power of a finite nonabelian simple group `S`, in three stages.  The **group side** produces the dual of a partition lattice as a congruence lattice: the interval `[D , Sᵐ]` is dually isomorphic to `Eq(m)`, and the WP-3 bridge of [FLRP.Bridge][] presents that interval as the decidable congruence lattice of the coset algebra.  The **algebra side** presents the congruences of `𝑨` as the partitions of its carrier invariant under finitely many index maps, so that cutting `Eq(m)` down to the invariant partitions cuts the coset algebra's congruences down to a copy of `DecCon 𝑨`, reversed.  The **assembly** expands the coset algebra by the lifted index maps and composes the stages into `DecCon 𝑬 ≅ dualLattice 𝑳`.

The submodules, in that order:

+  [FLRP.KurzweilNetter.Interval][]: Kurzweil's interval lemma, stated: the interval `[D , Sⁿ]`, the surjectivity statement in its two layers (the Layer-S statement of record, which the module's no-go theorem shows is excluded middle, and the decidable working form), the membership decider of the partition subgroups, the interval isomorphism `[D , Sⁿ] ≅ Eq(n)′` conditional on surjectivity, and the group representability of `Eq(n)′` that the wreath no-go consumes;
+  [FLRP.KurzweilNetter.Surjectivity][]: Kurzweil's interval lemma, proved: the blockwise collapse of [Classical.Structures.Group.PowerCollapse][] read through the interval vocabulary, giving the surjectivity family for every finite witnessed-nonabelian-simple base group and the unconditional decidable interval isomorphism;
+  [FLRP.KurzweilNetter.Invariance][]: partitions invariant under an index map, the notion where the algebra side and the group side of the construction meet;
+  [FLRP.KurzweilNetter.Blocks][]: decidable congruences of a finite carrier as partitions of its (irredundantly enumerated) index set, at the relation level;
+  [FLRP.KurzweilNetter.Translations][]: the basic translations of a finite finitary algebra, and the Mal'cev-style translation criterion identifying the congruences with the invariant partitions;
+  [FLRP.KurzweilNetter.Expansion][]: the expansion step showing the coset algebra on `Sᵐ/D`, expanded by a family of lifted index maps, has decidable congruence lattice dually isomorphic to the family-invariant partitions;
+  [FLRP.KurzweilNetter.Duality][]: the composite theorem `kurzweilNetterDuality`{.AgdaFunction}, parameterized by exactly the properties of the base group the argument uses, and its closure over the simple-group package (`kurzweilNetterDuality-ofSimple`{.AgdaFunction});
+  [FLRP.KurzweilNetter.A5][]: the instantiation at the certified `A₅`: `kurzweilNetterDuality-A₅`{.AgdaFunction}, a closed inhabitant of the theorem, together with the per-exponent surjectivity family.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.KurzweilNetter where

open import FLRP.KurzweilNetter.Interval      public
open import FLRP.KurzweilNetter.Surjectivity  public
open import FLRP.KurzweilNetter.Invariance    public
open import FLRP.KurzweilNetter.Blocks        public
open import FLRP.KurzweilNetter.Translations  public
open import FLRP.KurzweilNetter.Expansion     public
open import FLRP.KurzweilNetter.Duality       public
open import FLRP.KurzweilNetter.A5            public
```

--------------------------------------
