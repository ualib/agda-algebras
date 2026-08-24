---
layout: default
title : "Setoid.Functions module (Agda Universal Algebra Library)"
date : "2021-09-08"
author: "the agda-algebras development team"
---

## Setoid Functions

This is the [Setoid.Functions][] module of the [Agda Universal Algebra Library][].

This is a barrel module: it declares nothing of its own and re-exports the five
modules that develop functions between setoids.  A setoid function is a map
bundled with a proof that it respects the two equalities.  That proof is about a
single map, so it is only half of how the library does without function
extensionality; the other half is that wherever two functions must be compared,
an explicitly pointwise relation is used rather than propositional equality of
functions.  See `function-equality`{.AgdaFunction} of
[Setoid.Relations.Discrete][] and, for homomorphisms, `_≋_`{.AgdaFunction} of
[Setoid.Categories.Algebra][].

Reach for the following:

+  [Setoid.Functions.Basic][]: the identity, composition, and universe lifting of
   a setoid;
+  [Setoid.Functions.Injective][]: `IsInjective`{.AgdaFunction} and its
   composition law;
+  [Setoid.Functions.Surjective][]: `IsSurjective`{.AgdaFunction}, its
   composition law `⊙-IsSurjective`{.AgdaFunction}, the right inverse
   `SurjInv`{.AgdaFunction} of a surjection, and `epic-factor`{.AgdaFunction}.
   The decidable-index projections `proj`{.AgdaFunction} and
   `projIsOnto`{.AgdaFunction} that `ProjAlgIsOnto`{.AgdaFunction} of
   [Setoid.Algebras.Products][] consumes are *not* here; they are bare-types
   results in [Overture.Functions][];
+  [Setoid.Functions.Inverses][]: images and ranges, `Image_∋_`{.AgdaDatatype}
   and `IsInRange`{.AgdaFunction};
+  [Setoid.Functions.Bijective][]: `IsBijective`{.AgdaFunction} as
   injective-and-surjective, with the inverse `BijInv`{.AgdaFunction}.



```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Functions where

open import Setoid.Functions.Basic       public
open import Setoid.Functions.Bijective   public
open import Setoid.Functions.Injective   public
open import Setoid.Functions.Inverses    public
open import Setoid.Functions.Surjective  public
```
