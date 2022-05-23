---
layout: default
title : "Base module"
date : "2021-12-12"
author: "the agda-algebras development team"
---

### <a id="the-base-module-of-the-agda-universal-algebra-library">The Base Module of the Agda Universal Algebra Library</a>

This module collects all submodules the library that use "bare" types, as opposed to similar versions of these submodules based on Setoids (see the [Setoid](Setoid.html) module).

(We have also started developing in parallel the `cubical-agda-algebras` library, based on Cubical Agda.)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Base where

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


