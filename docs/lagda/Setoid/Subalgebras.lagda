---
layout: default
title : "Setoid.Subalgebras module (The Agda Universal Algebra Library)"
date : "2021-07-26"
author: "agda-algebras development team"
---

### <a id="subalgebra-setoid-types">Subalgebras over setoids</a>

This is the [Setoid.Subalgebras][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Subalgebras {𝑆 : Signature 𝓞 𝓥} where

open import Setoid.Subalgebras.Subuniverses  {𝑆 = 𝑆} public
open import Setoid.Subalgebras.Subalgebras   {𝑆 = 𝑆} public
open import Setoid.Subalgebras.Properties    {𝑆 = 𝑆} public
\end{code}

---------------------------------

<span style="float:left;">[← Setoid.Terms.Properties](Setoid.Terms.Properties.html)</span>
<span style="float:right;">[Setoid.Subalgebras.Subuniverses →](Setoid.Subalgebras.Subuniverses.html)</span>

{% include UALib.Links.md %}
