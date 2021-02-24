---
layout: default
title : UALib.Algebras module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

## <a id="algebra-types">Algebra Types</a>

This chapter presents the [UALib.Algebras][] module of the [Agda Universal Algebra Library][], which begins our [Agda][] formalization of the basic concepts and theorems of universal algebra. In this module we codify such notions as operation, signature, and algebraic structure.

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
