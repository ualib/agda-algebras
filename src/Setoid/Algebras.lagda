---
layout: default
title : "Setoid.Algebras module (Agda Universal Algebra Library)"
date : "2021-09-17"
author: "agda-algebras development team"
---

### <a id="setoid-representation-of-algebras">Setoid Representation of Algebras</a>

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Base.Signatures using (𝓞 ; 𝓥 ; Signature)

module Setoid.Algebras {𝑆 : Signature 𝓞 𝓥} where

 open import Setoid.Algebras.Basic        {𝑆  = 𝑆} public
 open import Setoid.Algebras.Products     {𝑆  = 𝑆} public
 open import Setoid.Algebras.Congruences  {𝑆  = 𝑆} public

\end{code}

--------------------------------

<span style="float:left;">[← Setoid.Relations.Quotients](Setoid.Relations.Quotients.html)</span>
<span style="float:right;">[Setoid.Algebras.Basic →](Setoid.Algebras.Basic.html)</span>

{% include UALib.Links.md %}
