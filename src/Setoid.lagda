---
layout: default
title : "Setoid module"
date : "2021-12-12"
author: "the agda-algebras development team"
---

## <a id="setoid-types-for-general-algebra">Setoid Types for General Algebra</a>

This module collects all submodule of that part of the library based on setoids,
as opposed to "bare" types (see [Base.lagda][]).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Setoid where

open import Setoid.Relations
open import Setoid.Functions
open import Setoid.Algebras
open import Setoid.Homomorphisms
open import Setoid.Terms
open import Setoid.Subalgebras
open import Setoid.Varieties
\end{code}

--------------------------------------

<span style="float:left;">[↑ Top](index.html)</span>
<span style="float:right;">[Setoid.Relations →](Setoid.Relations.html)</span>


{% include UALib.Links.md %}
