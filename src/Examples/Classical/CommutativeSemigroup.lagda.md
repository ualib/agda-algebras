---
layout: default
file: "src/Examples/Classical/CommutativeSemigroup.lagda.md"
title: "Examples.Classical.CommutativeSemigroup module"
date: "2026-05-24"
author: "the agda-algebras development team"
---

### Worked Example: `(ℕ, +, 0)` as a commutative semigroup

This is the [Examples.Classical.CommutativeSemigroup][] module of the [Agda Universal Algebra Library][].

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}
module Examples.Classical.CommutativeSemigroup where

open import Data.Nat                               using ( ℕ ; _+_ )
open import Data.Nat.Properties                    using ( +-assoc ; +-comm )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl )

open import Classical.Small.Structures.CommutativeSemigroup
  using ( CommutativeSemigroup ; eqsToCommutativeSemigroup )

import Classical.Structures.CommutativeSemigroup as Polymorphic
```
-->

```agda
ℕ-commutativeSemigroup : CommutativeSemigroup
ℕ-commutativeSemigroup = eqsToCommutativeSemigroup ℕ _+_ +-assoc +-comm

open Polymorphic.CommutativeSemigroup-Op ℕ-commutativeSemigroup using ( _∙_ )

∙-is-+-cs : ∀ (a b : ℕ) → a ∙ b ≡ a + b
∙-is-+-cs a b = refl
```
