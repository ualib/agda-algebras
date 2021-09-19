---
layout: default
title : "Relations module (The Agda Universal Algebra Library)"
date : "2021-01-12"
author: "the agda-algebras development team"
---

## <a id="relations">Relations</a>

This is the [Relations][] module of the [Agda Universal Algebra Library][].

In the [Relations.Discrete][] submodule we define types that represent *unary* and *binary relations*, which we refer to as "discrete relations" to contrast them with the ("continuous") *general* and *dependent relations* that we introduce in [Relations.Continuous][]. We call the latter "continuous relations" because they can have arbitrary arity (general relations) and they can be defined over arbitrary families of types (dependent relations).
Finally, in [Relations.Quotients][] we define quotient types.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Relations where

open import Relations.Discrete
open import Relations.Continuous
open import Relations.Properties
open import Relations.Quotients
open import Relations.Func

\end{code}

-------------------------------------

<span style="float:left;">[← Overture.Func.Bijective](Overture.Func.Bijective.html)</span>
<span style="float:right;">[Relations.Discrete →](Relations.Discrete.html)</span>

{% include UALib.Links.md %}
