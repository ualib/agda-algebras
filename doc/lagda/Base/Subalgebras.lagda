---
layout: default
title : "Base.Subalgebras module (The Agda Universal Algebra Library)"
date : "2021-01-14"
author: "agda-algebras development team"
---

## <a id="subalgebra-types">Subalgebra Types</a>

This is the [Base.Subalgebras][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( Signature ; 𝓞 ; 𝓥 )

module Base.Subalgebras {𝑆 : Signature 𝓞 𝓥} where

open import Base.Subalgebras.Subuniverses  {𝑆 = 𝑆} public
open import Base.Subalgebras.Subalgebras   {𝑆 = 𝑆} public
open import Base.Subalgebras.Properties    {𝑆 = 𝑆} public
\end{code}

--------------------------------------

<span style="float:left;">[← Base.Terms.Properties](Base.Terms.Properties.html)</span>
<span style="float:right;">[Base.Subalgebras.Subuniverses →](Base.Subalgebras.Subuniverses.html)</span>

{% include UALib.Links.md %}
