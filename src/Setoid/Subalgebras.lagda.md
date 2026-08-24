---
layout: default
title : "Setoid.Subalgebras module (The Agda Universal Algebra Library)"
date : "2021-07-26"
author: "agda-algebras development team"
---

### Subalgebras over setoids

This is the [Setoid.Subalgebras][] module of the [Agda Universal Algebra Library][].

This is a barrel module: it declares nothing of its own and re-exports the five
modules that make up the theory of subalgebras over setoids.  An algebra `𝑨` is a
**subalgebra** of `𝑩`, written `𝑨 ≤ 𝑩`, when `𝑨` can be homomorphically embedded
in `𝑩`, that is, when some homomorphism from `𝑨` to `𝑩` has an injective
underlying map.  Taking subalgebras is one of the three closure operations whose
composite defines a variety, and `S`{.AgdaFunction} of
[Setoid.Varieties.Closure][] is defined directly in terms of the
`_≤_`{.AgdaFunction} introduced here.

Reach for the following:

+  [Setoid.Subalgebras.Basic][]: the relation `_≤_`{.AgdaFunction}, its converse
   `_≥_`{.AgdaFunction}, the bundled `SubalgebraOf`{.AgdaRecord} and
   `Subalgebra`{.AgdaFunction} forms, the class-relative `_≤c_`{.AgdaFunction},
   and `mon→≤`{.AgdaFunction};
+  [Setoid.Subalgebras.Properties][]: that `_≤_`{.AgdaFunction} is a preorder,
   how it interacts with isomorphism and with universe lifting, and that it is
   preserved by products;
+  [Setoid.Subalgebras.Subuniverses][]: the subsets of a carrier closed under the
   operations, the subuniverse they generate, and the induction principle that
   makes generation usable;
+  [Setoid.Subalgebras.CompleteLattice][]: the subuniverses of a fixed algebra,
   ordered by inclusion, as a complete lattice;
+  [Setoid.Subalgebras.Subdirect][]: subdirect products, subdirect
   irreducibility, and Birkhoff's subdirect representation theorem, which is
   proved relative to a choice principle in general and unconditionally for
   finite algebras.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Subalgebras where

open import Setoid.Subalgebras.Basic public
open import Setoid.Subalgebras.CompleteLattice public
open import Setoid.Subalgebras.Properties public
open import Setoid.Subalgebras.Subuniverses public
open import Setoid.Subalgebras.Subdirect public
```
