---
layout: default
file: "src/Setoid/Subalgebras/Subdirect.lagda.md"
title: "Setoid.Subalgebras.Subdirect module (The Agda Universal Algebra Library)"
date: "2026-06-20"
author: "the agda-algebras development team"
---

### Subdirect products

This is the [Setoid.Subalgebras.Subdirect][] module of the [Agda Universal Algebra Library][].

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Subalgebras.Subdirect {𝑆 : Signature 𝓞 𝓥} where

open import Setoid.Subalgebras.Subdirect.Basic {𝑆 = 𝑆} public
open import Setoid.Subalgebras.Subdirect.BirkhoffSI {𝑆 = 𝑆} public
open import Setoid.Subalgebras.Subdirect.Finite {𝑆 = 𝑆} public
open import Setoid.Subalgebras.Subdirect.Irreducible {𝑆 = 𝑆} public
```
