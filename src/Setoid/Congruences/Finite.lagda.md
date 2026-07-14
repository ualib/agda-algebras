---
layout: default
title : "Setoid.Congruences.Finite module (Agda Universal Algebra Library)"
date : "2026-07-13"
author: "agda-algebras development team"
---

### Finitely enumerable congruence lattices

This is the [Setoid.Congruences.Finite][] module of the [Agda Universal Algebra Library][].

[Setoid.Congruences.Finite.Basic][] supplies the finiteness interface for congruences, that is,
*decidable congruences* (`DecCon`{.AgdaFunction}) and the record type `FiniteCongruences`{.AgdaRecord}.

[Setoid.Congruences.Finite.Decidable][] supplies the *constructive* counterpart:
a finite list of `DecCon`{.AgdaFunction}s that is complete — every
*decidable* congruence is `≑` to a listed one — with **no classical axiom**.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Congruences.Finite {𝑆 : Signature 𝓞 𝓥} where

open import Setoid.Congruences.Finite.Basic      {𝑆 = 𝑆} public
open import Setoid.Congruences.Finite.Decidable  {𝑆 = 𝑆} public
```
