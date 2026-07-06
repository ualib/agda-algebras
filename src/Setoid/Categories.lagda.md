---
layout: default
title : "Setoid.Categories module"
date : "2026-06-19"
author: "the agda-algebras development team"
---

## Categories for General Algebra

This module collects modules that formalize some of the basic notions of
category theory that are useful for formalizing universal algebra in other modules of
the library.


```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Categories where

open import Setoid.Categories.Adjunction public
open import Setoid.Categories.Algebra public
open import Setoid.Categories.Category public
open import Setoid.Categories.FullSubcategory public
open import Setoid.Categories.Functor public
open import Setoid.Categories.Monad public
open import Setoid.Categories.NaturalTransformation public
open import Setoid.Categories.Reduct public
```
