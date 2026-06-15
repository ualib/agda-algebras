---
layout: default
file: "src/Examples/Classical/Semigroup.lagda.md"
title: "Examples.Classical.Semigroup module"
date: "2026-05-18"
author: "the agda-algebras development team"
---

### Worked example: `(ℕ, +)` as a semigroup {#examples-classical-semigroup}

This is the [Examples.Classical.Semigroup][] module of the [Agda Universal Algebra Library][].

The natural numbers under addition form the canonical first semigroup to exhibit,
mirroring the magma example in [`Examples.Classical.Magma`][].  Beyond demonstrating
that the M3-4 deliverable type-checks, this module is the home for all future
semigroup-specific worked examples: alternative semigroups on `ℕ`, finite semigroups,
the free semigroup over a generating set, semigroups that fail to be monoids, and so on.
Subsequent additions should land here rather than alongside the core structure file.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Classical.Semigroup where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Data.Nat                               using ( ℕ ; _+_ )
open import Data.Nat.Properties                    using ( +-assoc )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Bundles.Semigroup           using ( ⟨_⟩ˢᵍ ; ⟪_⟫ˢᵍ )
open import Classical.Small.Structures.Semigroup  using ( Semigroup ; eqsToSemigroup )
open import Examples.Classical.Magma              using ( ℕ-magma )

import Classical.Structures.Semigroup as Polymorphic
```

#### The semigroup `(ℕ, +)` {#N-semigroup}

We build `(ℕ, +)` directly from stdlib's `+-assoc`.  The `eqsToSemigroup` constructor
demands an associativity proof of exactly the shape
`∀ a b c → (a + b) + c ≡ a + (b + c)`, which is the type of `+-assoc` up to the
definitional equality `Associative _+_ = ∀ x y z → (x + y) + z ≡ x + (y + z)`.

```agda
ℕ-semigroup : Semigroup
ℕ-semigroup = eqsToSemigroup ℕ _+_ +-assoc

open Polymorphic.Semigroup-Op ℕ-semigroup using ( _∙_ )
```

#### Acceptance checks

`∙-Op` interpreted in `ℕ-semigroup` reduces definitionally to `_+_`: no opacity
from the `eqsToSemigroup` construction, from the factoring through
`opsToMagma`, or from the `Curry₂` wrapping in the inherited named accessor;
discharged by `refl`.

```agda
∙-is-+-sg : ∀ (a b : ℕ) → a ∙ b ≡ a + b
∙-is-+-sg a b = refl
```

The forgetful image of `ℕ-semigroup` is the magma `ℕ-magma` *on the nose*.
This holds because `eqsToSemigroup` is implemented as `opsToMagma _·_ , <proof>`,
so `semigroup→magma (eqsToSemigroup ℕ _+_ +-assoc)` reduces to `opsToMagma ℕ _+_`,
which is exactly the definition of `ℕ-magma`; discharged by `refl`.

```agda
forgetful-agrees : Polymorphic.semigroup→magma ℕ-semigroup ≡ ℕ-magma
forgetful-agrees = refl
```

The bundle bridge round-trips on `ℕ-semigroup` pointwise.  Both directions reduce
by `pair a b 0F ⇉ a` and `pair a b 1F ⇉ b`, so propositional `refl` discharges the
obligation at the curried form (per
[ADR-002 v2](../../docs/adr/002-classical-layer-design.md) §6.

```agda
open Polymorphic.Semigroup-Op ⟪ ⟨ ℕ-semigroup ⟩ˢᵍ ⟫ˢᵍ using () renaming ( _∙_ to _·_ )

roundtrip-ℕ-sg : ∀ (a b : ℕ) → a · b ≡ a + b
roundtrip-ℕ-sg a b = refl
```

--------------------------------------

<span style="float:left;">[← Examples.Classical.Magma](Examples.Classical.Magma.html)</span>
<span style="float:right;">[Demos →](Demos.html)</span>

{% include UALib.Links.md %}
