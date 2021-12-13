---
layout: default
title : "Base module"
date : "2021-12-12"
author: "the agda-algebras development team"
---

### <a id="the-agda-universal-algebra-library-base-module">The Base Module of the Agda Universal Algebra Library</a>

This module collects all submodule of that part of the library that use "bare" types, as opposed to Setoids (see Setoid.lagda) or Cubical Agda (see Cubical.lagda).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Base.Overture where

open import Base.Overture
open import Base.Relations
open import Base.Algebras
open import Base.Equality
open import Base.Homomorphisms
open import Base.Terms
open import Base.Subalgebras
open import Base.Varieties
open import Base.Structures
open import Base.Adjunction
open import Base.Categories
open import Base.Complexity

\end{code}

--------------------------------------

<span style="float:left;">[← Preface](Preface.html)</span>
<span style="float:right;">[Base.Overture →](Base.Overture.html)</span>


