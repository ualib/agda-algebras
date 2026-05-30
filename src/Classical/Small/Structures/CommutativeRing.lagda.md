---
layout: default
file: "src/Classical/Small/Structures/CommutativeRing.lagda.md"
title: "Classical.Small.Structures.CommutativeRing module"
date: "2026-05-30"
author: "the agda-algebras development team"
---

### Level-fixed Commutative Ring

This is the [Classical.Small.Structures.CommutativeRing][] module of the [Agda Universal Algebra Library][].

Specializes [`Classical.Structures.CommutativeRing`][] to the `0ℓ`–`0ℓ` case,
mirroring the veneers of `Ring`, `CommutativeMonoid`, `AbelianGroup`, etc.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Small.Structures.CommutativeRing where

open import Agda.Primitive                          using () renaming ( Set to Type )
open import Level                                   using ( 0ℓ ; suc )
open import Relation.Binary.PropositionalEquality   using ( _≡_ )

import Classical.Structures.CommutativeRing as Polymorphic

CommutativeRing : Type (suc 0ℓ)
CommutativeRing = Polymorphic.CommutativeRing 0ℓ 0ℓ

eqsToCommutativeRing : (A : Type 0ℓ) (_+'_ : A → A → A) (0' : A) (-'_ : A → A) (_*'_ : A → A → A) (1' : A)
  → (∀ a b c → (a +' b) +' c ≡ a +' (b +' c))
  → (∀ a → 0' +' a ≡ a) → (∀ a → a +' 0' ≡ a)
  → (∀ a → (-' a) +' a ≡ 0') → (∀ a → a +' (-' a) ≡ 0')
  → (∀ a b → a +' b ≡ b +' a)
  → (∀ a b c → (a *' b) *' c ≡ a *' (b *' c))
  → (∀ a → 1' *' a ≡ a) → (∀ a → a *' 1' ≡ a)
  → (∀ a b → a *' b ≡ b *' a)
  → (∀ a b c → a *' (b +' c) ≡ (a *' b) +' (a *' c))
  → (∀ a b c → (b +' c) *' a ≡ (b *' a) +' (c *' a))
  → CommutativeRing
eqsToCommutativeRing = Polymorphic.eqsToCommutativeRing
```

--------------------------------------

<span style="float:left;">[← Classical.Small.Structures.Ring](Classical.Small.Structures.Ring.html)</span>

{% include UALib.Links.md %}
