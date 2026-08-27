---
layout: default
file: "src/Overture/Terms.lagda.md"
title: "Terms module"
date: "2026-06-18"
author: "the agda-algebras development team"
---

## Terms

This is the [Overture.Terms][] module of the [Agda Universal Algebra Library][].

A barrel over the term machinery, parameterized by a signature `𝑆` that it passes
to [Overture.Terms.Basic][] for the `Term` type and its level shorthand `ov`.
[Overture.Terms.Interpretation][] gives theory interpretations, sending operation
symbols to derived terms, and [Overture.Terms.Translation][] translates terms
along a signature morphism.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture.Signatures using ( 𝓞 ; 𝓥 ; Signature )
module Overture.Terms {𝑆 : Signature 𝓞 𝓥} where

open import Overture.Terms.Basic  {𝑆 = 𝑆}  public
open import Overture.Terms.Interpretation  public
open import Overture.Terms.Translation     public
```
