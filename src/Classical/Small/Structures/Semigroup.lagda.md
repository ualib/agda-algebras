---
layout: default
file: "src/Classical/Small/Structures/Semigroup.lagda.md"
title: "Classical.Small.Structures.Semigroup module"
date: "2026-05-18"
author: "the agda-algebras development team"
---

### Level-fixed Semigroups

This is the [Classical.Small.Structures.Semigroup][] module of the [Agda Universal Algebra Library][].

This module specializes [`Classical.Structures.Semigroup`][] to the common case where
the universe level of both the carrier and the equivalence is `0ℓ` (i.e., Set-valued
carriers with propositional or set-truncated equivalence).  The motivation matches
the corresponding magma veneer in [`Classical.Small.Structures.Magma`][]:
finite-template CSP, finite cases relevant to [FLRP][] intuition, and tutorial contexts
in [`Examples/`][Examples] and [`Demos/`][Demos] live in this small case, and pulling
the level-fixed specialization out keeps the polymorphic core unencumbered.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Small.Structures.Semigroup where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ----------------------------
open import Level                                  using ( 0ℓ ; suc )
open import Relation.Binary.PropositionalEquality  using ( _≡_ )

-- Imports from the Agda Universal Algebra Library ----------------------------
import Classical.Structures.Semigroup as Polymorphic
```

#### The Level-fixed Semigroup Type

```agda
Semigroup : Type (suc 0ℓ)
Semigroup = Polymorphic.Semigroup 0ℓ 0ℓ
```

#### Small `eqsToSemigroup`

The polymorphic `eqsToSemigroup` specializes immediately: with `α = 0ℓ`, it produces
a `Polymorphic.Semigroup 0ℓ 0ℓ` from `(A : Type 0ℓ)`, a binary operation, and an
associativity proof, which is exactly the level-fixed `Semigroup` above.

```agda
eqsToSemigroup  : (A : Type 0ℓ) (_·_ : A → A → A)
  → (∀ a b c → (a · b) · c ≡ a · (b · c))
  → Semigroup
eqsToSemigroup A = Polymorphic.eqsToSemigroup {A = A}
```
