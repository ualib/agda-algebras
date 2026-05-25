---
layout: default
file: "src/Classical/Small/Structures/Monoid.lagda.md"
title: "Classical.Small.Structures.Monoid module"
date: "2026-05-24"
author: "the agda-algebras development team"
---

### <a id="classical-small-monoid">Level-fixed monoid veneer</a>

This is the [Classical.Small.Structures.Monoid][] module of the [Agda Universal Algebra Library][].

Specializes [`Classical.Structures.Monoid`][] to the `0ℓ`–`0ℓ` case, mirroring the
magma and semigroup veneers.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Small.Structures.Monoid where

open import Agda.Primitive                          using () renaming ( Set to Type )
open import Level                                   using ( 0ℓ ; suc )
open import Relation.Binary.PropositionalEquality   using ( _≡_ )

import Classical.Structures.Monoid as Polymorphic

Monoid : Type (suc 0ℓ)
Monoid = Polymorphic.Monoid 0ℓ 0ℓ

fromMonoidEqs : (A : Type 0ℓ) (_·_ : A → A → A) (e : A)
  → (∀ a b c → (a · b) · c ≡ a · (b · c))
  → (∀ a → e · a ≡ a) → (∀ a → a · e ≡ a)
  → Monoid
fromMonoidEqs = Polymorphic.fromMonoidEqs
```

--------------------------------------

<span style="float:left;">[← Classical.Small.Structures.Semigroup](Classical.Small.Structures.Semigroup.html)</span>
<span style="float:right;">[Examples.Classical.Monoid →](Examples.Classical.Monoid.html)</span>

{% include UALib.Links.md %}
