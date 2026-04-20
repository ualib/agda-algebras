---
layout: default
title : "Setoid.Homomorphisms module (The Agda Universal Algebra Library)"
date : "2021-09-17"
author: "agda-algebras development team"
---

### <a id="types-for-homomorphism-of-setoid-algebras">Types for Homomorphism of Setoid Algebras</a>

This is the [Setoid.Homomorphisms][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Homomorphisms {𝑆 : Signature 𝓞 𝓥} where

open import Setoid.Homomorphisms.Basic              {𝑆 = 𝑆} public
open import Setoid.Homomorphisms.Properties         {𝑆 = 𝑆} public
open import Setoid.Homomorphisms.Kernels            {𝑆 = 𝑆} public
open import Setoid.Homomorphisms.Products           {𝑆 = 𝑆} public
open import Setoid.Homomorphisms.Noether            {𝑆 = 𝑆} public
open import Setoid.Homomorphisms.Factor             {𝑆 = 𝑆} public
open import Setoid.Homomorphisms.Isomorphisms       {𝑆 = 𝑆} public
open import Setoid.Homomorphisms.HomomorphicImages  {𝑆 = 𝑆} public

\end{code}

--------------------------------

<span style="float:left;">[← Setoid.Algebras.Congruences](Setoid.Algebras.Congruences.html)</span>
<span style="float:right;">[Setoid.Homomorphisms.Basic →](Setoid.Homomorphisms.Basic.html)</span>

{% include UALib.Links.md %}
