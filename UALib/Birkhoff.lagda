---
layout: default
title : UALib.Birkhoff module (Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

## <a id="birkhoffs-theorem">Birkhoff's Theorem</a>

This chapter presents the [UALib.Birkhoff][] module of the [Agda Universal Algebra Library][].

Here we give a formal proof in [MLTT][] of Birkhoff's theorem which says that a variety is an equational class. In other terms, a class 𝒦 of algebras is closed under the operators `H`, `S`, and `P` if and only if 𝒦 is the class of algebras that satisfy some set of identities.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UALib.Birkhoff where

open import UALib.Birkhoff.FreeAlgebra
open import UALib.Birkhoff.HSPTheorem

\end{code}

--------------------------------------

[← UALib.Varieties.Preservation](UALib.Varieties.Preservation.html)
<span style="float:right;">[UALib.Birkhoff.FreeAlgebra →](UALib.Birkhoff.FreeAlgebra.html)</span>

{% include UALib.Links.md %}
