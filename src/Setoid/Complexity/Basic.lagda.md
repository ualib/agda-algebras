---
layout: default
title : "Setoid.Complexity.Basic module (The Agda Universal Algebra Library)"
date : "2026-05-09"
author: "agda-algebras development team"
---

### Complexity Theory

This is the [Setoid.Complexity.Basic][] module of the [Agda Universal Algebra Library][].

This module is the canonical home for the content previously developed in `Legacy.Base.Complexity.Basic`, ported under #307 (M2-7c).  Its present scope is the prose definitions of words, algorithms, and polynomial-time computability that frame the CSP development in [`Setoid.Complexity.CSP`](Setoid.Complexity.CSP.html); concrete Agda content is intentionally deferred to #274 (M7-1, "Extend Complexity module beyond Basic and CSP"), which is the substantive sequel to this canonical-path migration.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Complexity.Basic where
```

#### Words

Let 𝑇ₙ be a totally ordered set of size 𝑛.  Let 𝐴 be a set (the alphabet).
We can model the set 𝑊ₙ, of *words* (strings of letters from 𝐴) of length 𝑛
by the type 𝑇ₙ → 𝐴 of functions from 𝑇ₙ to 𝐴.

The set of all (finite length) words is then

\[ W = ⋃[n ∈ ℕ] Wₙ \]

The *length* of a word 𝑥 is given by the function `size x`, which will be defined below.

An *algorithm* is a computer program with infinite memory (i.e., a Turing machine).

A function 𝑓 : 𝑊 → 𝑊 is *computable in polynomial time* if there exist an
algorithm and numbers 𝑐, 𝑑 ∈ ℕ such that for each word 𝑥 ∈ 𝑊 the algorithm
stops in at most (size 𝑥) 𝑐 + 𝑑 steps and computes 𝑓 𝑥.

At first we will simplify by assuming 𝑇ₙ is `Fin n`.

--------------------------------

<span style="float:left;">[↑ Setoid.Complexity](Setoid.Complexity.html)</span>
<span style="float:right;">[Setoid.Complexity.CSP →](Setoid.Complexity.CSP.html)</span>

{% include UALib.Links.md %}
