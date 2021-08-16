---
layout: default
title : Algebras module (Agda Universal Algebra Library)
date : 2021-01-12
author: [agda-algebras development team][]
---

## Algebra Types

This is the [Algebras][] module of the [Agda Universal Algebra Library][]. Here we use type theory and [Agda][] to codify the most basic objects of universal algebra, such as types in Agda *signatures* ([Algebras.Signatures][]), *algebras* ([Algebras.Algebras][]), *product algebras* ([Algebras.Products][]), *congruence relations* and *quotient algebras* ([Algebras.Congruences][]).


A popular way to represent algebraic structures in type theory is with record types.  The Sigma type (defined in [Overture.Preliminaries][]) provides an equivalent alternative that we happen to prefer and we use it throughout the library, both for consistency and because of its direct connection to the existential quantifier of logic. Recall from the Sigma types section of [Overture.Preliminaries][] that the type `Σ x ꞉ X , P x` represents the proposition, "there exists `x` in `X` such that `P x` holds;" in symbols, `∃ x ∈ X , P x`.  Indeed, an inhabitant of `Σ x ꞉ X , P x` is a pair `(x , p)` such that `x` inhabits `X` and `p` is a proof of `P x`. In other terms, the pair `(x , p)` is a witness and proof of the proposition `∃ x ∈ X , P x`.


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Algebras where

open import Algebras.Basic
open import Algebras.Products
open import Algebras.Congruences
open import Algebras.Setoid

\end{code}

-------------------------------------

{% include UALib.Links.md %}

--------------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

