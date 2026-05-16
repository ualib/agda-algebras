---
layout: default
file: "src/Classical/Small/Structures/Semigroup.lagda.md"
title: "Classical.Small.Structures.Semigroup module"
date: "2026-05-15"
author: "the agda-algebras development team"
---

### <a id="classical-small-structures-semigroup">Semigroups at `ℓ₀`</a>

This is the [Classical.Small.Structures.Semigroup][] module of the [Agda Universal Algebra Library][].

The level-fixed veneer of [`Classical.Structures.Semigroup`][Classical.Structures.Semigroup], specializing both the carrier-level `α` and the equivalence-level `ρ` to `lzero`.  This is the import path for downstream consumers (M7 finite-template CSP, M6 FLRP finite cases, tutorial `Examples/` and `Demos/`) where universe polymorphism is a distraction at use sites.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Small.Structures.Semigroup where

open import Agda.Primitive  using ()  renaming ( Set to Type )
open import Level           using ()  renaming ( 0ℓ to ℓ₀ )

import Classical.Structures.Semigroup as Poly

-- The level-fixed semigroup type.
Semigroup : Type _
Semigroup = Poly.Semigroup ℓ₀ ℓ₀

-- The level-fixed fromPropEq.  Builds a small semigroup from a Set, a
-- binary operation, and a propositional-equality associativity proof.
open import Relation.Binary.PropositionalEquality using ( _≡_ )

fromPropEq :  (A : Type)
              (_·_ : A → A → A)
              (·-assoc : ∀ a b c → ((a · b) · c) ≡ (a · (b · c)))
              → Semigroup
fromPropEq = Poly.fromPropEq
```

--------------------------------------

{% include UALib.Links.md %}
