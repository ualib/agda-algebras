---
layout: default
file: "src/Classical/Small/Structures/Monoid.lagda.md"
title: "Classical.Small.Structures.Monoid module"
date: "2026-05-24"
author: "the agda-algebras development team"
---

### Level-fixed Monoid

This is the [Classical.Small.Structures.Monoid][] module of the [Agda Universal Algebra Library][].

Specializes [`Classical.Structures.Monoid`][] to the common case where the universe
level of both the carrier and the equivalence is `0ℓ` (i.e., Set-valued carriers with
propositional or set-truncated equivalence), mirroring the analogous veneers for
`Magma`, `Semigroup`, etc.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Small.Structures.Monoid where

open import Agda.Primitive                         using () renaming ( Set to Type )
open import Level                                  using ( 0ℓ ; suc )
open import Relation.Binary.PropositionalEquality  using ( _≡_ )

import Classical.Structures.Monoid as Polymorphic

Monoid : Type (suc 0ℓ)
Monoid = Polymorphic.Monoid 0ℓ 0ℓ

eqsToMonoid : (A : Type 0ℓ) (_·_ : A → A → A) (e : A)
  → (∀ a b c → (a · b) · c ≡ a · (b · c))
  → (∀ a → e · a ≡ a) → (∀ a → a · e ≡ a)
  → Monoid
eqsToMonoid A = Polymorphic.eqsToMonoid {A = A}
```

--------------------------------------

<span style="float:left;">[← Classical.Small.Structures.Semigroup](Classical.Small.Structures.Semigroup.html)</span>
<span style="float:right;">[Examples.Classical.Monoid →](Examples.Classical.Monoid.html)</span>

{% include UALib.Links.md %}
