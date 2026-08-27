---
layout: default
title : "Examples.Demos module"
date : "2022-04-27"
author: "the agda-algebras development team"
---

## Demos of the Agda Algebras Library

This is the [Examples.Demos][] module of the [Agda Universal Algebra Library][].

Three self-contained demonstrations:
[Examples.Demos.GeneralOperationsAndRelations][] is a linked index of the general
operations-and-relations vocabulary; [Examples.Demos.HSP][] is the frozen literate
artifact of the TYPES 2021 paper, a machine-checked proof of Birkhoff's variety
theorem; and [Examples.Demos.ContraX][] is a cautionary counterexample from an
early formalization attempt.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Demos where

open import Examples.Demos.GeneralOperationsAndRelations
open import Examples.Demos.HSP
open import Examples.Demos.ContraX
```
