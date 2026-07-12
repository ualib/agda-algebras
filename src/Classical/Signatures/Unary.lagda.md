---
layout: default
file: "src/Classical/Signatures/Unary.lagda.md"
title: "Classical.Signatures.Unary module"
date: "2026-07-11"
author: "the agda-algebras development team"
---

### The purely unary signature on a set of symbols

This is the [Classical.Signatures.Unary][] module of the [Agda Universal Algebra Library][].

`Sig-Unary Ops` is the signature whose operation symbols are the elements of a
given type `Ops`, every symbol of arity one.  Unlike the fixed finite signatures of
this subtree (`Sig-Magma`, `Sig-Group`, …), the symbol set is a *parameter*: the
motivating instance takes `Ops` to be the carrier of a group `G`, which turns a
G-set into an ordinary unary algebra with one basic operation per group element.

Because a `Sig-Unary`-algebra is an `Algebra`{.AgdaRecord} like any other, the whole
congruence machinery (`Con`{.AgdaFunction}, quotients, homomorphism theorems) applies
to G-sets with no special cases.

The arity of every symbol is `Fin 1`, matching the convention of the unary symbol
`⁻¹-Op` in [`Sig-Group`][Classical.Signatures.Group].

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Signatures.Unary where

open import Agda.Primitive using ( Level ) renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base using ( Fin )
open import Data.Product  using ( _,_ )
open import Level         using ( 0ℓ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Overture.Signatures using ( Signature )
```
-->

```agda
-- The signature with symbol set Ops, every symbol unary.
Sig-Unary : {𝓞 : Level} → Type 𝓞 → Signature 𝓞 0ℓ
Sig-Unary Ops = Ops , λ _ → Fin 1
```
