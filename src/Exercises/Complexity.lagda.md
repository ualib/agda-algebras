---
layout: default
title : "Exercises.Complexity module"
date : "2022-18-06"
author: "the agda-algebras development team"
---

### Exercises in complexity theory

This is the [Exercises.Complexity][] module of the [Agda Universal Algebra Library][].

One module so far: [Exercises.Complexity.FiniteCSP][], constraint-satisfaction
exercises over small finite relational structures, created by Libor Barto for
students at Charles University and formalized here.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Exercises.Complexity where

open import Exercises.Complexity.FiniteCSP
```
