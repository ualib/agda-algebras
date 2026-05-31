---
layout: default
file: "src/Classical/Small/Structures/Group.lagda.md"
title: "Classical.Small.Structures.Group module"
date: "2026-05-30"
author: "the agda-algebras development team"
---

### Level-fixed Group

This is the [Classical.Small.Structures.Group][] module of the [Agda Universal Algebra Library][].

Specializes [`Classical.Structures.Group`][] to the common case where the universe
level of both the carrier and the equivalence is `0ℓ` (i.e., Set-valued carriers with
propositional or set-truncated equivalence), mirroring the analogous veneers for
`Magma`, `Semigroup`, `Monoid`, etc.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Small.Structures.Group where

open import Agda.Primitive                          using () renaming ( Set to Type )
open import Level                                   using ( 0ℓ ; suc )
open import Relation.Binary.PropositionalEquality   using ( _≡_ )

import Classical.Structures.Group as Polymorphic

Group : Type (suc 0ℓ)
Group = Polymorphic.Group 0ℓ 0ℓ

eqsToGroup : (A : Type 0ℓ) (_·_ : A → A → A) (e : A) (i : A → A)
  → (∀ a b c → (a · b) · c ≡ a · (b · c))
  → (∀ a → e · a ≡ a) → (∀ a → a · e ≡ a)
  → (∀ a → (i a) · a ≡ e) → (∀ a → a · (i a) ≡ e)
  → Group
eqsToGroup = Polymorphic.eqsToGroup
```

--------------------------------------

<span style="float:left;">[← Classical.Small.Structures.Monoid](Classical.Small.Structures.Monoid.html)</span>
<span style="float:right;">[Classical.Small.Structures.AbelianGroup →](Classical.Small.Structures.AbelianGroup.html)</span>

{% include UALib.Links.md %}
