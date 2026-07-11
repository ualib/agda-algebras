---
layout: default
file: "src/Classical/Small/Structures/Semilattice.lagda.md"
title: "Classical.Small.Structures.Semilattice module"
date: "2026-05-27"
author: "the agda-algebras development team"
---

### Level-fixed Semilattice

This is the [Classical.Small.Structures.Semilattice][] module of the [Agda Universal Algebra Library][].

Specializes [`Classical.Structures.Semilattice`][Classical.Structures.Semilattice] to the `0ℓ`–`0ℓ` case, mirroring
the veneers of `Magma`, `Semigroup`, `CommutativeSemigroup`, etc.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}
module Classical.Small.Structures.Semilattice where
open import Agda.Primitive                          using () renaming ( Set to Type )
open import Level                                   using ( 0ℓ ; suc )
open import Relation.Binary.PropositionalEquality   using ( _≡_ )
import Classical.Structures.Semilattice as Polymorphic
```
-->

```agda
Semilattice : Type (suc 0ℓ)
Semilattice = Polymorphic.Semilattice 0ℓ 0ℓ

eqsToSemilattice : (A : Type 0ℓ) (_·_ : A → A → A)
  → (∀ a b c → (a · b) · c ≡ a · (b · c))
  → (∀ a b → a · b ≡ b · a)
  → (∀ a → a · a ≡ a)
  → Semilattice
eqsToSemilattice = Polymorphic.eqsToSemilattice
```
