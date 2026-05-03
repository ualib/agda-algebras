---
layout: default
title : "Base module"
date : "2021-12-12"
author: "the agda-algebras development team"
---

## <a id="the-base-module-of-the-agda-universal-algebra-library">The Base Module of the Agda Universal Algebra Library</a>

This module collects all submodules the library that use "bare" types, as opposed to similar versions of these submodules based on Setoids (see the [Setoid][] module).

(We have also started developing in parallel the `cubical-agda-algebras` library, based on Cubical Agda.)


```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Legacy.Base where

open import Legacy.Base.Relations
open import Legacy.Base.Functions
open import Legacy.Base.Equality
open import Legacy.Base.Adjunction
open import Legacy.Base.Algebras
open import Legacy.Base.Homomorphisms
open import Legacy.Base.Terms
open import Legacy.Base.Subalgebras
open import Legacy.Base.Varieties
open import Legacy.Base.Structures
open import Legacy.Base.Categories
open import Legacy.Base.Complexity
```


--------------------------------------

<span style="float:left;">[↑ agda-algebras](index.html)</span>
<span style="float:right;">[Base.Relations →](Base.Relations.html)</span>


{% include UALib.Links.md %}
