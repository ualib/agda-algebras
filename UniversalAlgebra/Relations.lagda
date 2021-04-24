---
layout: default
title : Relations module (The Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

## <a id="relation-and-quotient-types">Relation and Quotient Types</a>

This is the [UniversalAlgebra.Relations][] module of the [Agda Universal Algebra Library][].

In [Relations.Discrete][] we define types that represent *unary* and *binary relations*, which we refer to as "discrete relations" to contrast them with the ("continuous") *general* and *dependent relations* that we introduce in [Relations.Continuous][]. We call the latter "continuous relations" because they can have arbitrary arity (general relations) and they can be defined over arbitrary families of types (dependent relations).


\begin{code}[hide]
{-# OPTIONS --without-K --exact-split --safe #-}
\end{code}

\begin{code}
module Relations where

open import Relations.Discrete public
open import Relations.Continuous public
open import Relations.Quotients public
open import Relations.Truncation public
open import Relations.Extensionality public

\end{code}


-------------------------------------

<p></p>

[← Overture.Lifts](Overture.Lifts.html)
<span style="float:right;">[Relations.Discrete →](Relations.Discrete.html)</span>

{% include UALib.Links.md %}
