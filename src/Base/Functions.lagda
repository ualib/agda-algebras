---
layout: default
title : "Base.Functions module (Agda Universal Algebra Library)"
date : "2021-01-12"
author: "the agda-algebras development team"
---

## <a id="overture">Overture</a>

This is the [Base.Functions][] module of the [Agda Universal Algebra Library][].

The source code for this module comprises the (literate) [Agda][] program that was
used to generate the html page displaying the sentence you are now reading. This
source code inhabits the file [Base/Overture.lagda][], which resides in the
[git repository of the agda-algebras library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Base.Functions where

open import Base.Functions.Inverses       public
open import Base.Functions.Injective      public
open import Base.Functions.Surjective     public
open import Base.Functions.Transformers   public

\end{code}

--------------------------------------

<span style="float:left;">[← Base](Base.html)</span>
<span style="float:right;">[Base.Functions.Preliminaries →](Base.Functions.Basic.html)</span>

{% include UALib.Links.md %}
