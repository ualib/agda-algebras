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
representability).  [FLRP.Closure.Basic][] is the umbrella over the two proved
theorems, [FLRP.Closure.Product][] for finite direct products and
[FLRP.Closure.OrdinalSum][] for glued ordinal sums, and derives its corollaries
from them: `adjoinBottom-Representableᵈ`, `adjoinTop-Representableᵈ`, and
`dual-Representableᵈ`, the last conditional on a Kurzweil–Netter duality
hypothesis.  The unglued ordinal sum appears there as a recipe (glue `chain₂`
between the summands), not as an exported theorem.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.Closure where

open import FLRP.Closure.Basic public
open import FLRP.Closure.Product public
open import FLRP.Closure.OrdinalSum public
```
