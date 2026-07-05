---
layout: default
title : "Setoid.Congruences module (Agda Universal Algebra Library)"
date : "2021-09-17"
author: "agda-algebras development team"
---

### Congruences


```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Congruences {𝑆 : Signature 𝓞 𝓥} where

open import Setoid.Congruences.Basic {𝑆 = 𝑆} public
open import Setoid.Congruences.ChainJoin   public
open import Setoid.Congruences.CompleteLattice {𝑆 = 𝑆} public
open import Setoid.Congruences.Generation {𝑆 = 𝑆} public
open import Setoid.Congruences.Lattice {𝑆 = 𝑆} public
open import Setoid.Congruences.Monolith {𝑆 = 𝑆} public
open import Setoid.Congruences.Properties {𝑆 = 𝑆} public
open import Setoid.Congruences.Permutability {𝑆 = 𝑆} public
```
