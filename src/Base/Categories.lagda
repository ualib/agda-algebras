---
layout: default
title : "Base.Categories module (The Agda Universal Algebra Library)"
date : "2021-08-31"
author: "agda-algebras development team"
---

## <a id="categories">Categories</a>

This is the [Base.Categories][] module of the [Agda Universal Algebra Library][].

This module is intended, not to replace or override anything in the [agda-categories][] library, but rather to collect some experiments in the use of category theory to re-express some of the basic concepts from universal algebra developed in other modules of the agda-algebra library.

The purpose of this effort twofold. First, we hope it makes the types defined in the agda-algebras library more modular and reusable.  Second, we hope that the more general language of category theory will make metaprogramming easier.  Somewhat ironically, one of our main motivations for metaprogramming is to help automate the task of recognizing when we have multiple alternative definitions (or proofs) of a single concept (or theorem) in the library and to potentially remove or consolidate such redundancy.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Base.Categories where

open import Base.Categories.Functors

\end{code}

--------------------------------------

<span style="float:left;">[← Base.Adjunction.Galois](Base.Adjunction.Galois.html)</span>
<span style="float:right;">[Base.Categories.Functors →](Base.Categories.Functors.html)</span>

{% include UALib.Links.md %}
