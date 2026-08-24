---
layout: default
title : "Setoid.Terms module (The Agda Universal Algebra Library)"
date : "2021-09-18"
author: "agda-algebras development team"
---

### Terms on setoids

This is the [Setoid.Terms][] module of the [Agda Universal Algebra Library][].

A **term** over a set `X` of variables is a formal expression built from those
variables by applying operation symbols of the signature.  Terms are the syntax
that equational logic is about, and the term algebra `𝑻 X`{.AgdaFunction} is the
free algebra on `X`: every assignment of values in an algebra to the variables
extends uniquely to a homomorphism out of `𝑻 X`.  That universal property is what
makes terms the bridge between syntax and semantics throughout the library.

This is a barrel module: it declares nothing of its own and re-exports the
following:

+  [Setoid.Terms.Basic][]: the term setoid and the algebra `𝑻`{.AgdaFunction},
   substitution, and environments;
+  [Setoid.Terms.Interpretation][]: the value of a term in an algebra under an
   environment;
+  [Setoid.Terms.Properties][]: the free lift, and uniqueness of the homomorphism
   it induces;
+  [Setoid.Terms.Operations][]: terms as operations on an algebra, and their
   behaviour on products and under homomorphisms;
+  [Setoid.Terms.Monad][]: the monad structure that substitution carries;
+  [Setoid.Terms.Translation][]: transporting terms along a signature morphism.


```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Terms where

open import Setoid.Terms.Basic  public
open import Setoid.Terms.Interpretation       public
open import Setoid.Terms.Monad  public
open import Setoid.Terms.Operations  public
open import Setoid.Terms.Properties  public
open import Setoid.Terms.Translation          public
```

(The two-signature modules [Setoid.Terms.Translation][] and
[Setoid.Terms.Interpretation][] relate two signatures at once, so they are not
`{𝑆}`-parameterized; they are nonetheless re-exported here for convenience.)
