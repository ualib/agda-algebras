---
layout: default
file: "src/FLRP/KurzweilNetter.lagda.md"
title: "FLRP.KurzweilNetter module (The Agda Universal Algebra Library)"
date: "2026-07-28"
author: "the agda-algebras development team"
---

### Kurzweil–Netter duality

This is the [FLRP.KurzweilNetter][] module of the [Agda Universal Algebra Library][].

This module develops the formal proof of the **Kurzweil–Netter duality theorem**,
which asserts that the class of decidably representable lattices is closed under
the taking of lattice duals.  It is assembled from the following submodules:

+  [FLRP.KurzweilNetter.Invariance][]: partitions invariant under an index map,
   the notion where the algebra side and the group side of the construction meet;
+  [FLRP.KurzweilNetter.Blocks][]: decidable congruences of a finite carrier as
   partitions of its (irredundantly enumerated) index set, at the relation level;
+  [FLRP.KurzweilNetter.Translations][]: the basic translations of a finite
   finitary algebra, and the Mal'cev-style translation criterion identifying the
   congruences with the invariant partitions;
+  [FLRP.KurzweilNetter.Expansion][]: the expansion step showing the coset algebra
   on `Sᵐ/D`, expanded by a family of lifted index maps, has decidable congruence
   lattice that is dually isomorphic to the family-invariant partitions;
+  [FLRP.KurzweilNetter.Duality][]: the composite theorem
   `kurzweilNetterDuality`{.AgdaFunction}, retiring Entry 2 of
   [FLRP.Assumptions][] to a proof from Entry 4 and the properties of a finite
   nontrivial group;
+  [FLRP.KurzweilNetter.A5][]: the instantiation at the certified `A₅`:
   `kurzweilNetterDuality-A₅`{.AgdaFunction}, a closed inhabitant of the
   theorem, together with the per-exponent surjectivity family.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.KurzweilNetter where

open import FLRP.KurzweilNetter.Invariance    public
open import FLRP.KurzweilNetter.Blocks        public
open import FLRP.KurzweilNetter.Translations  public
open import FLRP.KurzweilNetter.Expansion     public
open import FLRP.KurzweilNetter.Duality       public
open import FLRP.KurzweilNetter.A5            public
```

--------------------------------------
