---
layout: default
title : UALib.Birkhoff module (Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

## <a id="birkhoffs-theorem">Birkhoff's Theorem</a>

This chapter presents the [UALib.Birkhoff][] module of the [Agda Universal Algebra Library][].

Here we give a formal proof in [MLTT][] of Birkhoff's theorem &lt;birkhoffs theorem&gt;
(%s &lt;birkhoffs theorem&gt;), which says that a variety is an
equational class. In other terms, if a class 𝒦 of algebras is closed
under the operators 𝑯, 𝑺, 𝑷, then 𝒦 is an equational class (i.e., 𝒦 is
the class of algebras that model a particular set of identities). The
sections below contain (literate) Agda code that formalizes each step of
the (informal) proof we saw above in birkhoffs theorem.
\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UALib.Birkhoff where

open import UALib.Birkhoff.FreeAlgebra
open import UALib.Birkhoff.Lemmata
open import UALib.Birkhoff.Theorem

\end{code}

--------------------------------------

[← UALib.Varieties](UALib.Varieties.html)
<span style="float:right;">[Agda UALib TOC ↑](UALib.html)</span>


{% include UALib.Links.md %}
