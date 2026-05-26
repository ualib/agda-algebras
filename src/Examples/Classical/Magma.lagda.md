---
layout: default
file: "src/Examples/Classical/Magma.lagda.md"
title: "Examples.Classical.Magma module"
date: "2026-05-17"
author: "the agda-algebras development team"
---

### <a id="examples-classical-magma">Worked example — `(ℕ, +)` as a magma</a>

This is the [Examples.Classical.Magma][] module of the [Agda Universal Algebra Library][].

The natural numbers under addition form the canonical first magma to exhibit.
Beyond demonstrating that the M3-3 deliverable type-checks, this module is the
home for all future magma-specific worked examples: alternative magmas on `ℕ`
(under multiplication, under truncated subtraction), small finite magmas as Cayley
tables, free magmas over a generating set, magmas that fail to be semigroups,
and so on.  Subsequent additions should land here rather than alongside the
core structure file.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Classical.Magma where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Data.Nat                                using ( ℕ ; _+_ )
open import Relation.Binary.PropositionalEquality   using ( _≡_ ; refl )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Bundles.Magma             using ( ⟨_⟩ᵐᵃ ; ⟪_⟫ᵐᵃ )
open import Classical.Small.Structures.Magma    using ( Magma ; opsToMagma )
import      Classical.Structures.Magma          as Polymorphic
```

#### <a id="N-magma">The magma `(ℕ, +)`</a>

```agda
ℕ-magma : Magma
ℕ-magma = opsToMagma ℕ _+_

open Polymorphic.Magma-Op ℕ-magma using ( _∙_ )
```

#### <a id="acceptance">Acceptance checks</a>

`∙-Op` interpreted in `ℕ-magma` reduces definitionally to `_+_`: no opacity from
the `binaryOpToMagma` construction, no opacity from the `Curry₂` wrapping in the named
accessor.  Discharged by `refl`.

```agda
∙-is-+-ma : ∀ (a b : ℕ) → a ∙ b ≡ a + b
∙-is-+-ma a b = refl
```

The bundle bridge round-trips on `ℕ-magma` pointwise.  Both directions reduce by
`pair a b 0F ⇉ a` and `pair a b 1F ⇉ b`, so propositional `refl` discharges the
obligation at the curried form (per
[ADR-002 v2 §6](../../docs/adr/002-classical-layer-design.md)).

```agda
open Polymorphic.Magma-Op ⟪ ⟨ ℕ-magma ⟩ᵐᵃ ⟫ᵐᵃ using () renaming ( _∙_ to _·_ )

roundtrip-ℕ-ma : ∀ (a b : ℕ) → a · b ≡ a + b
roundtrip-ℕ-ma a b = refl
```

--------------------------------------

<span style="float:left;">[← Examples.Classical](Examples.Classical.html)</span>
<span style="float:right;">[Demos →](Demos.html)</span>

{% include UALib.Links.md %}
