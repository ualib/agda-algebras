---
layout: default
title : UALib.Varieties module (Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

## <a id="equations-and-varieties">Equations and Varieties</a>

This chapter presents the [UALib.Varieties][] module of the [Agda Universal Algebra Library][].

Here we define types for theories and their models and for equational logic.

A **variety** is a class of algebras, in the same signature, that is closed under the taking of homomorphic images, subalgebras, and arbitrary products.  To represent varieties we define inductive types for the closure operators `H`, `S`, and `P` that are composable.  Separately, we define an inductive type `V` which simultaneously represents closure under all three operators, `H`, `S`, and `P`.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UALib.Varieties where

open import UALib.Varieties.ModelTheory
open import UALib.Varieties.EquationalLogic
open import UALib.Varieties.Varieties
open import UALib.Varieties.Preservation

\end{code}

--------------------------------------

[← UALib.Subalgebras](UALib.Subalgebras.html)
<span style="float:right;">[UALib.Varieties.ModelTheory →](UALib.Varieties.ModelTheory.html)</span>

{% include UALib.Links.md %}
