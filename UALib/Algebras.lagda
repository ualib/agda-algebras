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

module UALib.Algebras where

open import UALib.Algebras.Signatures public
open import UALib.Algebras.Algebras public
open import UALib.Algebras.Products public
open import UALib.Algebras.Congruences

\end{code}

-------------------------------------

[← UALib.Relations.](UALib.Prelude.Extensionality.html)
<span style="float:right;">[UALib.Algebras.Signatures →](UALib.Algebras.Signatures.html)</span>

{% include UALib.Links.md %}
