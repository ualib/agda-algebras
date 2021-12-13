---
layout: default
title : "Base.Varieties module (Agda Universal Algebra Library)"
date : "2021-01-14"
author: "agda-algebras development team"
---

## <a id="equations-and-varieties">Equations and Varieties</a>

This is the [Base.Varieties][] module of the [Agda Universal Algebra Library][], where we define types for theories and their models, and for equational logic, and we prove properties of these types.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Base.Varieties where

open import Base.Varieties.EquationalLogic
open import Base.Varieties.Closure
open import Base.Varieties.Properties
open import Base.Varieties.Preservation
open import Base.Varieties.FreeAlgebras

\end{code}

---------------------------------

<span style="float:left;">[← Base.Subalgebras.Properties](Base.Subalgebras.Properties.html)</span>
<span style="float:right;">[Base.Varieties.EquationalLogic →](Base.Varieties.EquationalLogic.html)</span>

{% include UALib.Links.md %}
