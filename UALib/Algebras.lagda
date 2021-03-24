---
layout: default
title : Algebras module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

## <a id="algebra-types">Algebra Types</a>

This chapter presents the [Algebras][] module of the [Agda Universal Algebra Library][], which begins our [Agda][] formalization of the basic definitions and theorems of universal algebra. In this module we define types that codify the notions of operation, signature, algebra, product of algebras, congruence relation, and quotient algebra, and prove many of their basic properties.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Algebras where

open import Algebras.Signatures public
open import Algebras.Algebras public
open import Algebras.Products public
open import Algebras.Congruences

\end{code}

-------------------------------------

[← Relations.Truncation](Relations.Truncation.html)
<span style="float:right;">[Algebras.Signatures →](Algebras.Signatures.html)</span>

{% include UALib.Links.md %}
