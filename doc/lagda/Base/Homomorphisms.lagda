---
layout: default
title : "Base.Homomorphisms module (The Agda Universal Algebra Library)"
date : "2021-01-12"
author: "agda-algebras development team"
---

## <a id="homomorphism-types">Homomorphism Types</a>

This chapter presents the [Base.Homomorphisms][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (Signature ; 𝓞 ; 𝓥 )

module Base.Homomorphisms {𝑆 : Signature 𝓞 𝓥} where

open import Base.Homomorphisms.Basic              {𝑆 = 𝑆} public
open import Base.Homomorphisms.Properties         {𝑆 = 𝑆} public
open import Base.Homomorphisms.Kernels            {𝑆 = 𝑆} public
open import Base.Homomorphisms.Products           {𝑆 = 𝑆} public
open import Base.Homomorphisms.Noether            {𝑆 = 𝑆} public
open import Base.Homomorphisms.Factor             {𝑆 = 𝑆} public
open import Base.Homomorphisms.Isomorphisms       {𝑆 = 𝑆} public
open import Base.Homomorphisms.HomomorphicImages  {𝑆 = 𝑆} public
\end{code}

--------------------------------------

<span style="float:left;">[← Base.Algebras.Congruences](Base.Algebras.Congruences.html)</span>
<span style="float:right;">[Base.Homomorphisms.Basic →](Base.Homomorphisms.Basic.html)</span>

{% include UALib.Links.md %}
