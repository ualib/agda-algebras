---
layout: default
title : Varieties module (Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

## <a id="equations-and-varieties">Equations and Varieties</a>

This chapter presents the [Varieties][] module of the [Agda Universal Algebra Library][], where we define types for theories and their models and for equational logic and prove properties of these types.

Let 𝑆 be a signature. By an **identity** or **equation** in 𝑆 we mean an ordered pair of terms, written 𝑝 ≈ 𝑞, from the term algebra 𝑻 X. If 𝑨 is an 𝑆-algebra we say that 𝑨 **satisfies** 𝑝 ≈ 𝑞 provided 𝑝 ̇ 𝑨 ≡ 𝑞 ̇ 𝑨 holds. In this situation, we write 𝑨 ⊧ 𝑝 ≈ 𝑞 and say that 𝑨 **models** the identity 𝑝 ≈ q. If 𝒦 is a class of algebras, all of the same signature, we write 𝒦 ⊧ p ≈ q if, for every 𝑨 ∈ 𝒦, 𝑨 ⊧ 𝑝 ≈ 𝑞.

Because a class of structures has a different type than a single structure, we must use a slightly different syntax to avoid overloading the relations ⊧ and ≈. As a reasonable alternative to what we would normally express informally as 𝒦 ⊧ 𝑝 ≈ 𝑞, we have settled on 𝒦 ⊫ p ≈ q to denote this relation.  To reiterate, if 𝒦 is a class of 𝑆-algebras, we write 𝒦 ⊫ 𝑝 ≈ 𝑞 if every 𝑨 ∈ 𝒦 satisfies 𝑨 ⊧ 𝑝 ≈ 𝑞.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Varieties where

open import Varieties.Basic
open import Varieties.Properties
open import Varieties.Closure
open import Varieties.EquationalLogic
open import Varieties.Preservation
open import Varieties.FreeAlgebras

\end{code}


In the Varieties.Properties submodule we prove some closure and invariance properties of ⊧.

In the Varieties.Entailment submodule, we define the entailment relation and prove soundness and completeness of the entailment rules.




--------------------------------------

[← Subalgebras](Subalgebras.html)
<span style="float:right;">[Varieties.EquationalLogic →](Varieties.EquationalLogic.html)</span>

{% include UALib.Links.md %}
