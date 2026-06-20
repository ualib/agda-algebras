---
layout: default
title : "Setoid module"
date : "2021-12-12"
author: "the agda-algebras development team"
---

## Setoid Types for General Algebra

This module collects all submodule of that part of the library based on setoids,
as opposed to "bare" types (see [Base.lagda][]).


```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid where

open import Setoid.Algebras public
open import Setoid.Categories public
open import Setoid.Complexity public
open import Setoid.Congruences public
open import Setoid.Functions public
open import Setoid.Homomorphisms public
open import Setoid.Relations public
open import Setoid.Signatures public
open import Setoid.Subalgebras public
open import Setoid.Terms public
open import Setoid.Varieties public
```

--------------------------------------

<span style="float:left;">[↑ Top](index.html)</span>
<span style="float:right;">[Setoid.Relations →](Setoid.Relations.html)</span>


{% include UALib.Links.md %}
