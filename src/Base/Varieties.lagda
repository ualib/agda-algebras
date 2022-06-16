---
layout: default
title : "Base.Varieties module (Agda Universal Algebra Library)"
date : "2021-01-14"
author: "agda-algebras development team"
---

## <a id="equations-and-varieties">Equations and Varieties</a>

This is the [Base.Varieties][] module of the [Agda Universal Algebra Library][],
where we define types for theories and their models, and for equational logic,
and we prove properties of these types.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Base.Signatures using ( Signature ; 𝓞 ; 𝓥 )

module Base.Varieties {𝑆 : Signature 𝓞 𝓥} where

open import Base.Varieties.EquationalLogic  {𝑆 = 𝑆} public
open import Base.Varieties.Closure          {𝑆 = 𝑆} public
open import Base.Varieties.Properties       {𝑆 = 𝑆} public
open import Base.Varieties.Preservation     {𝑆 = 𝑆} public

open import Level using ( Level )

module _ {α : Level} where

 open import Base.Varieties.FreeAlgebras  {α = α} {𝑆 = 𝑆} public
\end{code}

---------------------------------

<span style="float:left;">[← Base.Subalgebras.Properties](Base.Subalgebras.Properties.html)</span>
<span style="float:right;">[Base.Varieties.EquationalLogic →](Base.Varieties.EquationalLogic.html)</span>

{% include UALib.Links.md %}
