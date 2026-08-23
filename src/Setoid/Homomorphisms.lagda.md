---
layout: default
title : "Setoid.Homomorphisms module (The Agda Universal Algebra Library)"
date : "2021-09-17"
author: "agda-algebras development team"
---

### Types for Homomorphism of Setoid Algebras

This is the [Setoid.Homomorphisms][] module of the [Agda Universal Algebra Library][].

This is a barrel module: it declares nothing of its own and re-exports the eight
modules that make up the theory of structure-preserving maps between setoid
algebras.

#### Submodule guide

+  [Setoid.Homomorphisms.Basic][]: `hom`{.AgdaFunction}, `mon`{.AgdaFunction},
   `epi`{.AgdaFunction}, their predicate forms, and the identity homomorphism;
+  [Setoid.Homomorphisms.Properties][]: composition, and the homomorphisms
   that witness universe lifting;
+  [Setoid.Homomorphisms.Kernels][]: the kernel congruence
   `kercon`{.AgdaFunction}, the quotient `kerquo`{.AgdaFunction}, and the
   canonical projection `πepi`{.AgdaFunction};
+  [Setoid.Homomorphisms.Products][]: the homomorphism into a product induced by a
   family of homomorphisms, and the coordinate projections out of one;
+  [Setoid.Homomorphisms.Noether][]: the first homomorphism theorem;
+  [Setoid.Homomorphisms.Factor][]: `HomFactor`{.AgdaFunction} (a homomorphism
   factors through any surjective homomorphism whose kernel is contained in its own);
+  [Setoid.Homomorphisms.Isomorphisms][]: `_≅_`{.AgdaRecord} and its interaction
   with products and with universe lifting;
+  [Setoid.Homomorphisms.HomomorphicImages][]: `_IsHomImageOf_`{.AgdaFunction} and
   the image algebra of a homomorphism.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Homomorphisms where

open import Setoid.Homomorphisms.Basic              public
open import Setoid.Homomorphisms.Kernels            public
open import Setoid.Homomorphisms.Products           public
open import Setoid.Homomorphisms.Noether            public
open import Setoid.Homomorphisms.Factor             public
open import Setoid.Homomorphisms.Isomorphisms       public
open import Setoid.Homomorphisms.HomomorphicImages  public
open import Setoid.Homomorphisms.Properties         public
```
