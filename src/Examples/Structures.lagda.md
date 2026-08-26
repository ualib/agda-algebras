---
layout: default
title : "Examples.Structures module"
date : "2022-18-06"
author: "the agda-algebras development team"
---

### Examples of structures

This is the [Examples.Structures][] module of the [Agda Universal Algebra Library][].

The structure examples exercise the general `structure` type of the frozen
`Legacy.Base` tree, which packages operation symbols and relation symbols in one
signature pair.  [Examples.Structures.Signatures][] supplies eight tiny signatures
named by an arity-counting convention, and [Examples.Structures.Basic][]
instantiates them with two structures: a three-element meet semilattice and the
NAE-3-SAT relational structure.  The signatures are also consumed by the
finite-CSP exercises of [Exercises.Complexity.FiniteCSP][].

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Structures where

open import Examples.Structures.Signatures  public
open import Examples.Structures.Basic       public
```
