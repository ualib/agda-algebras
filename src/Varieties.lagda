---
layout: default
title : "Varieties module (Agda Universal Algebra Library)"
date : "2021-01-14"
author: "agda-algebras development team"
---

## <a id="equations-and-varieties">Equations and Varieties</a>

This is the [Varieties][] module of the [Agda Universal Algebra Library][], where we define types for theories and their models, and for equational logic, and we prove properties of these types.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Varieties where

open import Varieties.EquationalLogic
open import Varieties.Closure
open import Varieties.Properties
open import Varieties.Preservation
open import Varieties.FreeAlgebras
open import Varieties.Func

\end{code}

---------------------------------

<span style="float:left;">[← Subalgebras.Func.Properties](Subalgebras.Func.Properties.html)</span>
<span style="float:right;">[Varieties.EquationalLogic →](Varieties.EquationalLogic.html)</span>

{% include UALib.Links.md %}
