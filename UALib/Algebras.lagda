---
layout: default
title : UALib.Algebras module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

## <a id="algebras">Algebras</a>

This chapter presents the [UALib.Algebras module][] of the [Agda Universal Algebra Library][].

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

[← UALib.Prelude](UALib.Prelude.html)
<span style="float:right;">[UALib.Relations →](UALib.Relations.html)</span>

{% include UALib.Links.md %}
