---
layout: default
file: "src/Classical/Structures/Lattice/Table.lagda.md"
title: "Classical.Structures.Lattice.Table module"
date: "2026-10-11"
author: "the agda-algebras development team"
---

### Finite lattices from tables

This is the [Classical.Structures.Lattice.Table][] module of the [Agda Universal Algebra Library][].

A small finite lattice is most easily given by its two operation tables, as the
worked groups of [Examples.Classical.Groups][] are given by their Cayley tables.
This module turns a pair of binary operations on `Fin n` into a
`Lattice`{.AgdaFunction} whose carrier is `Fin n` with propositional equality,
once the eight equations of `Th-Lattice`{.AgdaFunction} have been checked, and
equips it with the `FiniteAlgebra`{.AgdaRecord} structure that the finite decision
procedures of [Classical.Properties.Lattice.Semidistributive][] consume.

Each equation is decided by an exhaustive sweep (`all?`{.AgdaFunction} over
`Fin n`, once per variable, and `_≟_`{.AgdaFunction} on `Fin n` for each
instance), using the checkers of [Overture.Operations.Properties][].  The two
associative laws have `n³` instances each, the two commutative and the two
absorption laws `n²` each, and the two idempotent laws `n` each, so a table of `n`
elements costs `2n³ + 4n² + 2n` comparisons, each a few table lookups.  At
`n = 5`, the size of the lattices `M₃` and `N₅` of
[Examples.Classical.Lattices.M3][] and [Examples.Classical.Lattices.N5][], that is
360 comparisons, and the sweep is free.  The cubic term makes it expensive in the
tens.  The group precedent is the alternating group `A₅`, at `n = 60`: its
associative law alone is 216,000 instances, and deciding it by the sweep was
measured at 72 seconds and 13.8 GB of memory, which is why
[Examples.Classical.Groups.AlternatingGroup5][] derives associativity from a
faithful permutation action instead (the device that
[Classical.Structures.Group.TableGroup][] packages).  A lattice of that size
would want a similar device, such as building it order-first from a decidable
order, rather than a larger sweep.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Classical.Structures.Lattice.Table where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Properties                    using ( _≟_ )
open import Data.Nat.Base                          using ( ℕ )
open import Data.Product                           using ( _×_ ; _,_ ; proj₁ )
open import Level                                  using ( 0ℓ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl )
open import Relation.Nullary.Decidable.Core        using ( Dec ; _×-dec_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Lattice.Basic  using ( Lattice ; eqsToLattice )
open import Overture.Operations.Properties      using ( Associative? ; Commutative? ; Idempotent?
                                                      ; Absorbsˡ? ; Absorbsʳ? )
open import Setoid.Algebras.Finite              using ( FiniteAlgebra )
```
-->

#### The lattice laws of a pair of tables

`LatticeTableLaws _∧_ _∨_`{.AgdaFunction} is the conjunction of the eight
equations that `eqsToLattice`{.AgdaFunction} of
[Classical.Structures.Lattice.Basic][] asks for, in its order: associativity,
commutativity, and idempotence of each operation, and the two absorption laws in
the shapes `a ∧ (a ∨ b) ≡ a` and `(a ∧ b) ∨ a ≡ a` that `Th-Lattice`{.AgdaFunction}
states.  `latticeTableLaws?`{.AgdaFunction} decides the conjunction, one checker
per law.  For concrete tables, `from-yes` of the decision computes to the eight
proofs, or the definition that applies it fails to type-check if a table is wrong.

```agda
module _ {n : ℕ} (_∧_ _∨_ : Fin n → Fin n → Fin n) where

  LatticeTableLaws : Type
  LatticeTableLaws =
      (∀ a b c → (a ∧ b) ∧ c ≡ a ∧ (b ∧ c)) × (∀ a b → a ∧ b ≡ b ∧ a) × (∀ a → a ∧ a ≡ a)
    × (∀ a b c → (a ∨ b) ∨ c ≡ a ∨ (b ∨ c)) × (∀ a b → a ∨ b ≡ b ∨ a) × (∀ a → a ∨ a ≡ a)
    × (∀ a b → a ∧ (a ∨ b) ≡ a) × (∀ a b → (a ∧ b) ∨ a ≡ a)

  latticeTableLaws? : Dec LatticeTableLaws
  latticeTableLaws? =
    Associative? _∧_ ×-dec Commutative? _∧_ ×-dec Idempotent? _∧_
    ×-dec Associative? _∨_ ×-dec Commutative? _∨_ ×-dec Idempotent? _∨_
    ×-dec Absorbsˡ? _∧_ _∨_ ×-dec Absorbsʳ? _∧_ _∨_
```

#### The lattice and its finiteness

`tableLattice`{.AgdaFunction} hands the operations and the eight laws to
`eqsToLattice`{.AgdaFunction}, so its curried meet and join are the given
operations, definitionally.  Its carrier is `Fin n` itself, so the identity
enumerates it, and the equality `_≡_` on `Fin n` is decidable
(`tableLattice-FiniteAlgebra`{.AgdaFunction}).  The laws are an explicit argument
rather than a decision evaluated inside the constructor, so the constructor is
total for every pair of operations and the cost of checking a table is paid once,
where a concrete lattice is defined.

```agda
  tableLattice : LatticeTableLaws → Lattice 0ℓ 0ℓ
  tableLattice (∧-assoc , ∧-comm , ∧-idem , ∨-assoc , ∨-comm , ∨-idem , absorbˡ , absorbʳ) =
    eqsToLattice (Fin n) _∧_ _∨_ ∧-assoc ∧-comm ∧-idem ∨-assoc ∨-comm ∨-idem absorbˡ absorbʳ

  tableLattice-FiniteAlgebra : (laws : LatticeTableLaws) → FiniteAlgebra (proj₁ (tableLattice laws))
  tableLattice-FiniteAlgebra laws = record
    { _≟_       = _≟_
    ; card      = n
    ; enum      = λ i → i
    ; enum-sur  = λ x → x , refl
    }
```
