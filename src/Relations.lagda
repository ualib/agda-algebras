---
layout: default
title : Relations module (The Agda Universal Algebra Library)
date : 2021-01-12
author: [agda-algebras development team][]
---

## <a id="types-for-relations-and-quotients">Types for Relations and Quotients</a>

This is the [Relations][] module of the [Agda Universal Algebra Library][].

In the [Relations.Discrete][] submodule we define types that represent *unary* and *binary relations*, which we refer to as "discrete relations" to contrast them with the ("continuous") *general* and *dependent relations* that we introduce in [Relations.Continuous][]. We call the latter "continuous relations" because they can have arbitrary arity (general relations) and they can be defined over arbitrary families of types (dependent relations).
Finally, in [Relations.Quotients][] we define quotient types.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Relations where

open import Relations.Discrete public
open import Relations.Continuous public
open import Relations.Properties public
open import Relations.Quotients public

\end{code}

-------------------------------------

[← Overture.Transformers](Overture.Transformers.html)
<span style="float:right;">[Relations.Discrete →](Relations.Discrete.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
