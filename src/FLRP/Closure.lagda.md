---
layout: default
file: "src/FLRP/Closure.lagda.md"
title: "FLRP.Closure module (The Agda Universal Algebra Library)"
date: "2026-07-24"
author: "the agda-algebras development team"
---

### Closure properties of representability

This is the [FLRP.Closure][] module of the [Agda Universal Algebra Library][].

This is a barrel module for the closure toolkit: the operations under which the
class of representable lattices is closed, formalized at Layer D (decidable
representability).  [FLRP.Closure.Basic][] is the umbrella, deriving the corollary
closures (adjoined bottom, adjoined top, the unglued sum) from the two proved
theorems: [FLRP.Closure.Product][] for finite direct products and
[FLRP.Closure.OrdinalSum][] for glued ordinal sums.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.Closure where

open import FLRP.Closure.Basic public
open import FLRP.Closure.Product public
open import FLRP.Closure.OrdinalSum public
```
