---
layout: default
title : UALib.Relations module (The Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

[UALib ↑](UALib.html)

## <a id="relations">Relations</a>

This chapter presents the [UALib.Relations][] module of the [Agda Universal Algebra Library][].

\begin{code}[hide]
{-# OPTIONS --without-K --exact-split --safe #-}
\end{code}

\begin{code}
module UALib.Relations where

open import UALib.Relations.Unary public
open import UALib.Relations.Binary public
open import UALib.Relations.Equivalences public
open import UALib.Relations.Quotients public
open import UALib.Relations.Congruences public

\end{code}

--------------------------------------

{% include UALib.Links.md %}
