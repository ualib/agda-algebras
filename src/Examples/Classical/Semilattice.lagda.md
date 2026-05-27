---
layout: default
file: "src/Examples/Classical/Semilattice.lagda.md"
title: "Examples.Classical.Semilattice module"
date: "2026-05-27"
author: "the agda-algebras development team"
---

### Worked Example: `(Bool, _∧_)` as a semilattice

This is the [Examples.Classical.Semilattice][] module of the [Agda Universal Algebra Library][].

Booleans under conjunction form the canonical small semilattice — idempotent,
commutative, associative.  Built directly from stdlib's `∧-assoc`, `∧-comm`,
`∧-idem` in `Data.Bool.Properties`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}
module Examples.Classical.Semilattice where

open import Data.Bool                              using ( Bool ; _∧_ )
open import Data.Bool.Properties                   using ( ∧-assoc ; ∧-comm ; ∧-idem )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl )

open import Classical.Small.Structures.Semilattice
  using ( Semilattice ; eqsToSemilattice )

import Classical.Structures.Semilattice as Polymorphic

Bool-meet-semilattice : Semilattice
Bool-meet-semilattice = eqsToSemilattice Bool _∧_ ∧-assoc ∧-comm ∧-idem

open Polymorphic.Semilattice-Op Bool-meet-semilattice using ( _∙_ )

∙-is-∧-sl : ∀ (a b : Bool) → a ∙ b ≡ a ∧ b
∙-is-∧-sl a b = refl
```

--------------------------------------

{% include UALib.Links.md %}
