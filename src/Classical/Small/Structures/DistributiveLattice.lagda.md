---
layout: default
file: "src/Classical/Small/Structures/DistributiveLattice.lagda.md"
title: "Classical.Small.Structures.DistributiveLattice module"
date: "2026-05-31"
author: "the agda-algebras development team"
---

### Level-fixed Distributive Lattice

This is the [Classical.Small.Structures.DistributiveLattice][] module of the [Agda Universal Algebra Library][].

Specializes [`Classical.Structures.DistributiveLattice`][] to the `0ℓ`–`0ℓ` case,
mirroring the veneers of `Lattice`, `CommutativeMonoid`, etc.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}
module Classical.Small.Structures.DistributiveLattice where
open import Agda.Primitive                          using () renaming ( Set to Type )
open import Level                                   using ( 0ℓ ; suc )
open import Relation.Binary.PropositionalEquality   using ( _≡_ )
import Classical.Structures.DistributiveLattice as Polymorphic

DistributiveLattice : Type (suc 0ℓ)
DistributiveLattice = Polymorphic.DistributiveLattice 0ℓ 0ℓ

eqsToDistributiveLattice : (A : Type 0ℓ) (_∧'_ _∨'_ : A → A → A)
  → (∀ a b c → (a ∧' b) ∧' c ≡ a ∧' (b ∧' c))
  → (∀ a b → a ∧' b ≡ b ∧' a)
  → (∀ a → a ∧' a ≡ a)
  → (∀ a b c → (a ∨' b) ∨' c ≡ a ∨' (b ∨' c))
  → (∀ a b → a ∨' b ≡ b ∨' a)
  → (∀ a → a ∨' a ≡ a)
  → (∀ a b → a ∧' (a ∨' b) ≡ a)
  → (∀ a b → (a ∧' b) ∨' a ≡ a)
  → (∀ a b c → a ∧' (b ∨' c) ≡ (a ∧' b) ∨' (a ∧' c))
  → (∀ a b c → a ∨' (b ∧' c) ≡ (a ∨' b) ∧' (a ∨' c))
  → DistributiveLattice
eqsToDistributiveLattice = Polymorphic.eqsToDistributiveLattice
```

--------------------------------------

{% include UALib.Links.md %}
