---
layout: default
title : "Base.Overture module (Agda Universal Algebra Library)"
date : "2021-01-12"
author: "the agda-algebras development team"
---

## <a id="overture">Overture</a>

This is the [Base.Overture][] module of the [Agda Universal Algebra Library][].

The source code for this module comprises the (literate) [Agda][] program that was used to generate the html page displaying the sentence you are now reading. This source code inhabits the file [Base/Overture.lagda][], which resides in the [git repository of the agda-algebras library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Base.Overture where

open import Base.Overture.Preliminaries  public
open import Base.Overture.Inverses       public
open import Base.Overture.Injective      public
open import Base.Overture.Surjective     public
open import Base.Overture.Transformers   public

\end{code}

--------------------------------------

<span style="float:left;">[← Base](Base.html)</span>
<span style="float:right;">[Base.Overture.Preliminaries →](Base.Overture.Preliminaries.html)</span>

{% include UALib.Links.md %}
