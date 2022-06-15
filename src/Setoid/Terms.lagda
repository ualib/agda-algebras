---
layout: default
title : "Setoid.Terms module (The Agda Universal Algebra Library)"
date : "2021-09-18"
author: "agda-algebras development team"
---

### <a id="terms-on-setoids">Terms on setoids</a>

This is the [Setoid.Terms][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Base.Signatures using (𝓞 ; 𝓥 ; Signature)

module Setoid.Terms {𝑆 : Signature 𝓞 𝓥} where

open import Setoid.Terms.Basic       {𝑆 = 𝑆} public
open import Setoid.Terms.Properties  {𝑆 = 𝑆} public
open import Setoid.Terms.Operations  {𝑆 = 𝑆} public

\end{code}

--------------------------------

<span style="float:left;">[← Setoid.Homomorphisms.HomomorphicImages](Setoid.Homomorphisms.HomomorphicImages.html)</span>
<span style="float:right;">[Setoid.Terms.Basic →](Setoid.Terms.Basic.html)</span>

{% include UALib.Links.md %}
