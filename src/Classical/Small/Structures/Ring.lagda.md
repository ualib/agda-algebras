---
layout: default
file: "src/Classical/Small/Structures/Ring.lagda.md"
title: "Classical.Small.Structures.Ring module"
date: "2026-05-30"
author: "the agda-algebras development team"
---

### Level-fixed Ring

This is the [Classical.Small.Structures.Ring][] module of the [Agda Universal Algebra Library][].

Specializes [`Classical.Structures.Ring`][Classical.Structures.Ring] to the common case where the universe
level of both the carrier and the equivalence is `0ℓ` (i.e., Set-valued carriers with
propositional or set-truncated equivalence), mirroring the analogous veneers for
`Monoid`, `Group`, `Lattice`, etc.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Small.Structures.Ring where

open import Agda.Primitive                         using () renaming ( Set to Type )
open import Level                                  using ( 0ℓ ; suc )
open import Relation.Binary.PropositionalEquality  using ( _≡_ )

import Classical.Structures.Ring as Polymorphic
```
-->

```agda
Ring : Type (suc 0ℓ)
Ring = Polymorphic.Ring 0ℓ 0ℓ

eqsToRing : (A : Type 0ℓ) (_+'_ : A → A → A) (0' : A) (-'_ : A → A) (_*'_ : A → A → A) (1' : A)
  → (∀ a b c → (a +' b) +' c ≡ a +' (b +' c))
  → (∀ a → 0' +' a ≡ a) → (∀ a → a +' 0' ≡ a)
  → (∀ a → (-' a) +' a ≡ 0') → (∀ a → a +' (-' a) ≡ 0')
  → (∀ a b → a +' b ≡ b +' a)
  → (∀ a b c → (a *' b) *' c ≡ a *' (b *' c))
  → (∀ a → 1' *' a ≡ a) → (∀ a → a *' 1' ≡ a)
  → (∀ a b c → a *' (b +' c) ≡ (a *' b) +' (a *' c))
  → (∀ a b c → (b +' c) *' a ≡ (b *' a) +' (c *' a))
  → Ring
eqsToRing = Polymorphic.eqsToRing
```
