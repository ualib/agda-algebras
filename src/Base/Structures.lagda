---
layout: default
title : "Base.Structures module (Agda Universal Algebra Library)"
date : "2021-07-26"
author: "agda-algebras development team"
---

## <a id="types-for-general-mathematical-structures">Types for General Mathematical Structures</a>

This is the [Base.Structures][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Base.Structures where

open import Base.Structures.Basic            public
open import Base.Structures.Products         public
open import Base.Structures.Congruences      public
open import Base.Structures.Homs             public
open import Base.Structures.Graphs           public
open import Base.Structures.Graphs0
open import Base.Structures.Isos             public
open import Base.Structures.Terms            public
open import Base.Structures.Substructures    public
open import Base.Structures.EquationalLogic  public
open import Base.Structures.Sigma

\end{code}

--------------------------------

<span style="float:left;">[↑ Base](Base.html)</span>
<span style="float:right;">[Base.Structures.Basic →](Base.Structures.Basic.html)</span>

{% include UALib.Links.md %}
