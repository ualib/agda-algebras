---
layout: default
title : "Setoid.Homomorphisms module (The Agda Universal Algebra Library)"
date : "2021-09-17"
author: "agda-algebras development team"
---

### Types for Homomorphism of Setoid Algebras

This is the [Setoid.Homomorphisms][] module of the [Agda Universal Algebra Library][].

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature ; 𝑆)

module Setoid.Homomorphisms where

open import Setoid.Homomorphisms.Basic                       public
open import Setoid.Homomorphisms.Kernels                     public
open import Setoid.Homomorphisms.Products                    public
open import Setoid.Homomorphisms.Noether                     public
open import Setoid.Homomorphisms.Factor                      public
open import Setoid.Homomorphisms.Isomorphisms  public
open import Setoid.Homomorphisms.HomomorphicImages  public
open import Setoid.Homomorphisms.Properties                  public
```
