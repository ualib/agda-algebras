---
layout: default
title : UALib.Varieties module (Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

## <a id="equations-and-varieties">Equations and Varieties</a>

This chapter presents the [UALib.Varieties][] module of the [Agda Universal Algebra Library][].

Here we define type for for theories and their models, and equational logic.

A **variety** is a class of algebras, in the same signature, that is closed under the taking of homomorphic images, subalgebras, and arbitrary products.  To represent varieties we define inductive types for the closure operators H, S, P that are composable.  Separately, we define an inductive type `V` to represent closure under `H`, `S`, and `P`.

<!-- consequently, we expect that `V 𝒦 ≡ H (S (P 𝒦))` holds each class 𝒦 of algebras of a fixed signature. -->

\begin{code}[hide]
{-# OPTIONS --without-K --exact-split --safe #-}
\end{code}

\begin{code}

module UALib.Varieties where

open import UALib.Varieties.ModelTheory
open import UALib.Varieties.EquationalLogic
open import UALib.Varieties.Varieties
open import UALib.Varieties.Preservation

\end{code}

--------------------------------------

[← UALib.Subalgebras](UALib.Subalgebras.html)
<span style="float:right;">[UALib.Birkhoff →](UALib.Birkhoff.html)</span>

{% include UALib.Links.md %}
