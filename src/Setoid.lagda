---
layout: default
title : "Setoid module"
date : "2021-12-12"
author: "the agda-algebras development team"
---

### <a id="the-setoid-module-of-the-agda-universal-algebra-library">The Setoid Module of the Agda Universal Algebra Library</a>

This module collects all submodule of that part of the library based on setoids, as opposed to "bare" types (see Base.lagda), or Cubical Agda (used in the forthcoming `cubical-agda-algebras` library).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Setoid where

open import Setoid.Relations       public
open import Setoid.Functions       public
open import Setoid.Algebras        public
open import Setoid.Homomorphisms   public
open import Setoid.Terms           public
open import Setoid.Subalgebras     public
open import Setoid.Varieties       public

\end{code}

--------------------------------------

<span style="float:left;">[↑ Top](index.html)</span>
<span style="float:right;">[Setoid.Overture →](Setoid.Overture.html)</span>


