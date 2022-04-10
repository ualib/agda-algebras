---
layout: default
title : "Relations module (The Agda Universal Algebra Library)"
date : "2021-01-12"
author: "the agda-algebras development team"
---

## <a id="relations">Relations</a>

This is the [Base.Relations][] module of the [Agda Universal Algebra Library][].

In the [Base.Relations.Discrete][] submodule we define types that represent *unary* and *binary relations*, which we refer to as "discrete relations" to contrast them with the ("continuous") *general* and *dependent relations* that we introduce in [Base.Relations.Continuous][]. We call the latter "continuous relations" because they can have arbitrary arity (general relations) and they can be defined over arbitrary families of types (dependent relations).
Finally, in [Base.Relations.Quotients][] we define quotient types.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Base.Relations where

open import Base.Relations.Discrete
open import Base.Relations.Continuous
open import Base.Relations.Properties
open import Base.Relations.Quotients

\end{code}

-------------------------------------

<span style="float:left;">[← Base.Overture.Transformers](Base.Overture.Transformers.html)</span>
<span style="float:right;">[Base.Relations.Discrete →](Base.Relations.Discrete.html)</span>

{% include UALib.Links.md %}
