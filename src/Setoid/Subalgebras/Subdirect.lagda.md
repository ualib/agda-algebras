---
layout: default
file: "src/Setoid/Subalgebras/Subdirect.lagda.md"
title: "Setoid.Subalgebras.Subdirect module (The Agda Universal Algebra Library)"
date: "2026-06-20"
author: "the agda-algebras development team"
---

### Subdirect products

This is the [Setoid.Subalgebras.Subdirect][] module of the [Agda Universal Algebra Library][].

A **subdirect product** of a family of algebras is a subalgebra of their product
that projects *onto* every factor.  The surjective-projections condition is what
makes the notion useful: an arbitrary subalgebra of a product may ignore some
coordinates entirely, whereas a subdirect product retains information about each
one.  Subdirect decompositions are how a single algebra is analysed into simpler
pieces, and the pieces that cannot be decomposed further are the subdirectly
irreducible algebras.

This is a barrel module, re-exporting the following:

+  [Setoid.Subalgebras.Subdirect.Basic][]: `coord`{.AgdaFunction} for the
   coordinate homomorphisms of a map into a product,
   `SubdirectEmbedding`{.AgdaFunction} and `subdirect→≤`{.AgdaFunction}, and the
   bridge from a `Separates`{.AgdaFunction} family of congruences to a subdirect
   embedding via the natural map `natmap`{.AgdaFunction};
+  [Setoid.Subalgebras.Subdirect.Irreducible][]: the structural characterisation,
   relating injectivity of a coordinate map to its kernel lying
   `BelowDiagonal`{.AgdaFunction}, and `embed→separates`{.AgdaFunction};
+  [Setoid.Subalgebras.Subdirect.BirkhoffSI][]: the two statements
   `SubdirectlyRepresentable`{.AgdaFunction} and `SubdirectSIRep`{.AgdaFunction},
   the implication `SIRep→Representable`{.AgdaFunction} from the second to the
   first, and `Birkhoff-subdirect`{.AgdaFunction}.  That last is Birkhoff's
   subdirect representation theorem *relative to a choice principle*: it takes a
   module parameter supplying an SI-representation for every algebra, because
   producing one for an arbitrary algebra is a Zorn's-lemma step and so is not
   available postulate-free.  What that module proves outright is the choice-free
   core;
+  [Setoid.Subalgebras.Subdirect.Finite][]: the same theorem made unconditional for
   finite algebras.  `finiteSubdirectSIRep`{.AgdaFunction} constructs the
   SI-representation by search, with no choice and no postulate, and
   `finite-Birkhoff`{.AgdaFunction} feeds it to the choice-free core.  "Finite" has
   to be pinned down with some care, and that module opens by doing so.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Subalgebras.Subdirect where

open import Setoid.Subalgebras.Subdirect.Basic public
open import Setoid.Subalgebras.Subdirect.BirkhoffSI public
open import Setoid.Subalgebras.Subdirect.Finite public
open import Setoid.Subalgebras.Subdirect.Irreducible public
```
