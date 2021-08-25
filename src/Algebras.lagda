---
layout: default
title : Algebras module (Agda Universal Algebra Library)
date : 2021-01-12
author: [agda-algebras development team][]
---

## <a id="algebra-types">Algebra Types</a>

This is the [Algebras][] module of the [Agda Universal Algebra Library][] in which we use type theory and [Agda][] to codify the most basic objects of universal algebra, such as *signatures*, *algebras*, *product algebras*, *congruence relations*, and *quotient algebras*.


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Algebras where

open import Algebras.Basic
open import Algebras.Products
open import Algebras.Congruences
open import Algebras.Setoid

\end{code}

-------------------------------------

<br>
<br>

[← ClosureSystems.Properties](ClosureSystems.Properties.html)
<span style="float:right;">[Algebras.Basic →](Algebras.Basic.html)</span>


{% include UALib.Links.md %}


[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

