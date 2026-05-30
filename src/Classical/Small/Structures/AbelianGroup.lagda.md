---
layout: default
file: "src/Classical/Small/Structures/AbelianGroup.lagda.md"
title: "Classical.Small.Structures.AbelianGroup module"
date: "2026-05-30"
author: "the agda-algebras development team"
---

### Level-fixed Abelian Group

This is the [Classical.Small.Structures.AbelianGroup][] module of the [Agda Universal Algebra Library][].

Specializes [`Classical.Structures.AbelianGroup`][] to the `0ℓ`–`0ℓ` case, mirroring
the veneers of `Monoid`, `CommutativeMonoid`, `Group`, etc.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Small.Structures.AbelianGroup where

open import Agda.Primitive                          using () renaming ( Set to Type )
open import Level                                   using ( 0ℓ ; suc )
open import Relation.Binary.PropositionalEquality   using ( _≡_ )

import Classical.Structures.AbelianGroup as Polymorphic

AbelianGroup : Type (suc 0ℓ)
AbelianGroup = Polymorphic.AbelianGroup 0ℓ 0ℓ

eqsToAbelianGroup : (A : Type 0ℓ) (_·_ : A → A → A) (e : A) (i : A → A)
  → (∀ a b c → (a · b) · c ≡ a · (b · c))
  → (∀ a → e · a ≡ a) → (∀ a → a · e ≡ a)
  → (∀ a → (i a) · a ≡ e) → (∀ a → a · (i a) ≡ e)
  → (∀ a b → a · b ≡ b · a)
  → AbelianGroup
eqsToAbelianGroup = Polymorphic.eqsToAbelianGroup
```

--------------------------------------

<span style="float:left;">[← Classical.Small.Structures.Group](Classical.Small.Structures.Group.html)</span>

{% include UALib.Links.md %}
