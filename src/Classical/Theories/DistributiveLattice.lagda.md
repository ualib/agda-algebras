---
layout: default
file: "src/Classical/Theories/DistributiveLattice.lagda.md"
title: "Classical.Theories.DistributiveLattice module"
date: "2026-05-31"
author: "the agda-algebras development team"
---

### The equational theory of distributive lattices {#classical-theories-distributivelattice}

This is the [Classical.Theories.DistributiveLattice][] module of the [Agda Universal Algebra Library][].

`Th-DistributiveLattice` extends [`Th-Lattice`][Classical.Theories.Lattice] by two
distributivity equations over the same `Sig-Lattice` signature: the meet distributes
over the join (`∧-distribˡ`) and the join distributes over the meet (`∨-distribˡ`).
This is an *equation-only* extension — the signature is unchanged — exactly as
[`Th-CommutativeMonoid`][Classical.Theories.CommutativeMonoid] extends `Th-Monoid`.

Each of the two laws is stated in *left* form only.  In any lattice the two left
laws are interderivable, and each left law implies its right-handed companion by
commutativity; the structure module derives the right-handed and cross-operation
forms.  Carrying both left laws (rather than just one) keeps the theory self-dual
and mirrors the standard library's `IsDistributiveLattice`, which likewise records
`∨-distrib-∧` and `∧-distrib-∨` side by side rather than deriving one from the
other.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Theories.DistributiveLattice where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive                         using () renaming ( Set to Type )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Product                           using ( _×_ )
open import Relation.Binary.PropositionalEquality  using ( refl )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Signatures.Lattice      using  ( Sig-Lattice ; ∧-Op ; ∨-Op )
open import Classical.Equations               using  ( Associative ; Commutative
                                                     ; Idempotent ; AbsorbsLeft
                                                     ; AbsorbsRight ; DistributesOverˡ )
open import Overture.Terms {𝑆 = Sig-Lattice}  using  ( Term )

data Eq-DistributiveLattice : Type where
  ∧-assoc ∧-comm ∧-idem : Eq-DistributiveLattice
  ∨-assoc ∨-comm ∨-idem : Eq-DistributiveLattice
  absorbˡ absorbʳ       : Eq-DistributiveLattice
  ∧-distribˡ ∨-distribˡ : Eq-DistributiveLattice

Th-DistributiveLattice : Eq-DistributiveLattice → Term (Fin 3) × Term (Fin 3)
Th-DistributiveLattice ∧-assoc     = Associative       ∧-Op refl 0F 1F 2F
Th-DistributiveLattice ∧-comm      = Commutative       ∧-Op refl 0F 1F
Th-DistributiveLattice ∧-idem      = Idempotent        ∧-Op refl 0F
Th-DistributiveLattice ∨-assoc     = Associative       ∨-Op refl 0F 1F 2F
Th-DistributiveLattice ∨-comm      = Commutative       ∨-Op refl 0F 1F
Th-DistributiveLattice ∨-idem      = Idempotent        ∨-Op refl 0F
Th-DistributiveLattice absorbˡ     = AbsorbsLeft       ∧-Op ∨-Op refl refl 0F 1F
Th-DistributiveLattice absorbʳ     = AbsorbsRight      ∧-Op ∨-Op refl refl 0F 1F
Th-DistributiveLattice ∧-distribˡ  = DistributesOverˡ  ∧-Op ∨-Op refl refl 0F 1F 2F
Th-DistributiveLattice ∨-distribˡ  = DistributesOverˡ  ∨-Op ∧-Op refl refl 0F 1F 2F
```

Unfolding the distributivity builders (per [`Classical.Equations`][]):
`Th-DistributiveLattice ∧-distribˡ` is the pair

    (node ∧-Op (pair (ℊ 0F)
                     (node ∨-Op (pair (ℊ 1F) (ℊ 2F))))
    , node ∨-Op (pair (node ∧-Op (pair (ℊ 0F) (ℊ 1F)))
                      (node ∧-Op (pair (ℊ 0F) (ℊ 2F)))))

— i.e. `x ∧ (y ∨ z) ≈ (x ∧ y) ∨ (x ∧ z)` — and `∨-distribˡ` is its dual
`x ∨ (y ∧ z) ≈ (x ∨ y) ∧ (x ∨ z)`.

--------------------------------------

{% include UALib.Links.md %}
