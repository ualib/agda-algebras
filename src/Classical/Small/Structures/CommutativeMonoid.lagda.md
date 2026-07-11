---
layout: default
file: "src/Classical/Small/Structures/CommutativeMonoid.lagda.md"
title: "Classical.Small.Structures.CommutativeMonoid module"
date: "2026-05-24"
author: "the agda-algebras development team"
---

### Level-fixed Commutative Monoid

This is the [Classical.Small.Structures.CommutativeMonoid][] module of the [Agda Universal Algebra Library][].

Specializes [`Classical.Structures.CommutativeMonoid`][Classical.Structures.CommutativeMonoid] to the `0ℓ`–`0ℓ` case, mirroring the veneers of
`Magma`, `Semigroup`, `Monoid`, etc.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}
module Classical.Small.Structures.CommutativeMonoid where
open import Agda.Primitive                          using () renaming ( Set to Type )
open import Level                                   using ( 0ℓ ; suc )
open import Relation.Binary.PropositionalEquality   using ( _≡_ )
import Classical.Structures.CommutativeMonoid as Polymorphic
```
-->

```agda
CommutativeMonoid : Type (suc 0ℓ)
CommutativeMonoid = Polymorphic.CommutativeMonoid 0ℓ 0ℓ

eqsToCommutativeMonoid : (A : Type 0ℓ) (_·_ : A → A → A) (e : A)
  → (∀ a b c → (a · b) · c ≡ a · (b · c))
  → (∀ a → e · a ≡ a) → (∀ a → a · e ≡ a)
  → (∀ a b → a · b ≡ b · a)
  → CommutativeMonoid
eqsToCommutativeMonoid = Polymorphic.eqsToCommutativeMonoid
```
