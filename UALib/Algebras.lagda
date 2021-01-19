---
layout: default
title : UALib.Algebras module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

## <a id="algebras">Algebras</a>

This chapter presents the [UALib.Algebras][] module of the [Agda Universal Algebra Library][], which begins our [Agda][] formalization of the basic concepts and theorems of universal algebra. In this module we codify such notions as operation, signature, and algebraic structure.

\begin{code}[hide]
{-# OPTIONS --without-K --exact-split --safe #-}
\end{code}

\begin{code}

module UALib.Algebras where

open import UALib.Algebras.Signatures public
open import UALib.Algebras.Algebras public
open import UALib.Algebras.Products public
open import UALib.Algebras.Lifts public

\end{code}

-------------------------------------

[← UALib.Prelude.Extensionality](UALib.Prelude.Extensionality.html)
<span style="float:right;">[UALib.Algebras.Signatures →](UALib.Algebras.Signatures.html)</span>

{% include UALib.Links.md %}
