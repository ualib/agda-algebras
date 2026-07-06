---
layout: default
file: "src/Classical/Small/Structures/Lattice.lagda.md"
title: "Classical.Small.Structures.Lattice module"
date: "2026-05-28"
author: "the agda-algebras development team"
---

### Level-fixed Lattice

This is the [Classical.Small.Structures.Lattice][] module of the [Agda Universal Algebra Library][].

Specializes [`Classical.Structures.Lattice`][] to the common case where the universe
level of both the carrier and the equivalence is `0ℓ` (i.e., Set-valued carriers with
propositional or set-truncated equivalence), mirroring the veneers of `Magma`,
`Semigroup`, `Monoid`, etc.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}
module Classical.Small.Structures.Lattice where
open import Agda.Primitive                         using () renaming ( Set to Type )
open import Level                                  using ( 0ℓ ; suc )
open import Relation.Binary.PropositionalEquality  using ( _≡_ )
import Classical.Structures.Lattice as Polymorphic
```
-->

```agda
Lattice : Type (suc 0ℓ)
Lattice = Polymorphic.Lattice 0ℓ 0ℓ

eqsToLattice : (A : Type 0ℓ) (_∧'_ _∨'_ : A → A → A)
  → (∀ a b c → (a ∧' b) ∧' c ≡ a ∧' (b ∧' c))
  → (∀ a b → a ∧' b ≡ b ∧' a)
  → (∀ a → a ∧' a ≡ a)
  → (∀ a b c → (a ∨' b) ∨' c ≡ a ∨' (b ∨' c))
  → (∀ a b → a ∨' b ≡ b ∨' a)
  → (∀ a → a ∨' a ≡ a)
  → (∀ a b → a ∧' (a ∨' b) ≡ a)
  → (∀ a b → (a ∧' b) ∨' a ≡ a)
  → Lattice
eqsToLattice = Polymorphic.eqsToLattice
```
