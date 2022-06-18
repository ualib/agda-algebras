---
layout: default
title : "Setoid.Overture module (Agda Universal Algebra Library)"
date : "2021-09-08"
author: "the agda-algebras development team"
---

## <a id="setoids-functions">Setoid Functions</a>

This is the [Setoid.Functions][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Setoid.Functions where

open import Setoid.Functions.Basic       public
open import Setoid.Functions.Inverses    public
open import Setoid.Functions.Injective   public
open import Setoid.Functions.Surjective  public
open import Setoid.Functions.Bijective   public

\end{code}

--------------------------------------

<span style="float:left;">[← Preface](Preface.html)</span>
<span style="float:right;">[Setoid.Functions.Preliminaries →](Setoid.Functions.Preliminaries.html)</span>

{% include UALib.Links.md %}
