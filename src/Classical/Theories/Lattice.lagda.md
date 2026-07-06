---
layout: default
file: "src/Classical/Theories/Lattice.lagda.md"
title: "Classical.Theories.Lattice module"
date: "2026-05-27"
author: "the agda-algebras development team"
---

### The equational theory of lattices

This is the [Classical.Theories.Lattice][] module of the [Agda Universal Algebra Library][].

`Th-Lattice` has eight equations: associativity, commutativity, and idempotency for
each of the two binary operations `∧-Op` and `∨-Op`, plus the two absorption laws
relating them.  All equations are composed from the generic builders of
[`Classical.Equations`][] applied to `Sig-Lattice`'s symbols.  The constructor
names hyphenate the operation as a prefix (`∧-assoc`, `∨-comm`, …) so that the
underlying operation is visible at every use site of the equational logic.

Idempotency is included as a separate equation despite being derivable from
absorption in any structure satisfying the rest (stdlib's `Algebra.Lattice.Structures.IsLattice`
omits it for that reason); the presentation is uniform with `Th-Semilattice` and
makes the bridge to `Algebra.Lattice.Bundles.Lattice`'s record cheaper in one
direction without preventing the derivation in the other.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Theories.Lattice where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive                         using () renaming ( Set to Type )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Product                           using ( _×_ )
open import Relation.Binary.PropositionalEquality  using ( refl )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Signatures.Lattice           using ( Sig-Lattice ; ∧-Op ; ∨-Op )
open import Classical.Equations                    using ( Associative ; Commutative ; Idempotent
                                                         ; AbsorbsLeft ; AbsorbsRight )
open import Overture.Terms {𝑆 = Sig-Lattice}       using ( Term )
```
-->

```agda
data Eq-Lattice : Type where
  ∧-assoc ∧-comm ∧-idem : Eq-Lattice
  ∨-assoc ∨-comm ∨-idem : Eq-Lattice
  absorbˡ absorbʳ       : Eq-Lattice

Th-Lattice : Eq-Lattice → Term (Fin 3) × Term (Fin 3)
Th-Lattice ∧-assoc = Associative  ∧-Op refl 0F 1F 2F
Th-Lattice ∧-comm  = Commutative  ∧-Op refl 0F 1F
Th-Lattice ∧-idem  = Idempotent   ∧-Op refl 0F
Th-Lattice ∨-assoc = Associative  ∨-Op refl 0F 1F 2F
Th-Lattice ∨-comm  = Commutative  ∨-Op refl 0F 1F
Th-Lattice ∨-idem  = Idempotent   ∨-Op refl 0F
Th-Lattice absorbˡ = AbsorbsLeft  ∧-Op ∨-Op refl refl 0F 1F
Th-Lattice absorbʳ = AbsorbsRight ∧-Op ∨-Op refl refl 0F 1F
```

Unfolding the absorption builders (per [`Classical.Equations`][]):
`Th-Lattice absorbˡ` is the pair
`(node ∧-Op (pair (ℊ 0F) (node ∨-Op (pair (ℊ 0F) (ℊ 1F)))) , ℊ 0F)` — i.e.
`x ∧ (x ∨ y) ≈ x` — and `Th-Lattice absorbʳ` is
`(node ∨-Op (pair (node ∧-Op (pair (ℊ 0F) (ℊ 1F))) (ℊ 0F)) , ℊ 0F)` — i.e.
`(x ∧ y) ∨ x ≈ x`.
