---
layout: default
file: "src/Classical/Theories/CommutativeSemigroup.lagda.md"
title: "Classical.Theories.CommutativeSemigroup module"
date: "2026-05-24"
author: "the agda-algebras development team"
---

### The equational theory of commutative semigroups

This is the [Classical.Theories.CommutativeSemigroup][] module of the [Agda Universal Algebra Library][].

A commutative semigroup adds commutativity to the semigroup theory, over the same
`Sig-Magma` signature (no new symbols).  `Th-CommutativeSemigroup` therefore has two
equations, both composed from the generic builders of [`Classical.Equations`][Classical.Equations].

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Theories.CommutativeSemigroup where

open import Agda.Primitive                         using () renaming ( Set to Type )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Product                           using ( _×_ )
open import Relation.Binary.PropositionalEquality  using ( refl )

open import Classical.Signatures.Magma             using ( Sig-Magma ; ∙-Op )
open import Classical.Equations                    using ( Associative ; Commutative )
open import Overture.Terms {𝑆 = Sig-Magma}         using ( Term )
```
-->

```agda
data Eq-CommutativeSemigroup : Type where
  assoc comm : Eq-CommutativeSemigroup

Th-CommutativeSemigroup : Eq-CommutativeSemigroup → Term (Fin 3) × Term (Fin 3)
Th-CommutativeSemigroup assoc = Associative ∙-Op refl 0F 1F 2F
Th-CommutativeSemigroup comm  = Commutative ∙-Op refl 0F 1F
```
