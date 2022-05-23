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

open import Setoid.Overture
open import Setoid.Relations
open import Setoid.Algebras
open import Setoid.Homomorphisms
open import Setoid.Terms
open import Setoid.Subalgebras
open import Setoid.Varieties

\end{code}

--------------------------------------

<span style="float:left;">[↑ Top](index.html)</span>
<span style="float:right;">[Setoid.Overture →](Setoid.Overture.html)</span>


