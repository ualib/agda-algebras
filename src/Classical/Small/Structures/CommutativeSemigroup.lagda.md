---
layout: default
file: "src/Classical/Small/Structures/CommutativeSemigroup.lagda.md"
title: "Classical.Small.Structures.CommutativeSemigroup module"
date: "2026-05-24"
author: "the agda-algebras development team"
---

### Level-fixed Commutative Semigroup

This is the [Classical.Small.Structures.CommutativeSemigroup][] module of the [Agda Universal Algebra Library][].

Specializes [`Classical.Structures.CommutativeSemigroup`][Classical.Structures.CommutativeSemigroup] to the `0ℓ`–`0ℓ` case, mirroring the veneers of
`Magma`, `Semigroup`, etc.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}
module Classical.Small.Structures.CommutativeSemigroup where
open import Agda.Primitive                          using () renaming ( Set to Type )
open import Level                                   using ( 0ℓ ; suc )
open import Relation.Binary.PropositionalEquality   using ( _≡_ )
import Classical.Structures.CommutativeSemigroup as Polymorphic
```
-->

```agda
CommutativeSemigroup : Type (suc 0ℓ)
CommutativeSemigroup = Polymorphic.CommutativeSemigroup 0ℓ 0ℓ

eqsToCommutativeSemigroup : (A : Type 0ℓ) (_·_ : A → A → A)
  → (∀ a b c → (a · b) · c ≡ a · (b · c))
  → (∀ a b → a · b ≡ b · a)
  → CommutativeSemigroup
eqsToCommutativeSemigroup = Polymorphic.eqsToCommutativeSemigroup
```
