---
layout: default
file: "src/Order/Iso.lagda.md"
title : "Order.Iso module (The Agda Universal Algebra Library)"
date : "2026-07-26"
author: "agda-algebras development team"
---

### Order isomorphisms

This is the [Order.Iso][] module of the [Agda Universal Algebra Library][].

An **order isomorphism** between two ordered objects is a pair of monotone maps that
are mutually inverse up to the respective equivalences.  Because both maps are
monotone and the round trips are the identity up to the equivalence, an order
isomorphism transports every existing infimum and supremum, so isomorphic posets
carry the same lattice (indeed, complete-lattice) structure; this is why no separate
preservation clauses for meet and join are needed.

`OrderIso`{.AgdaRecord} states this for *raw relations* rather than for a bundle, so
it applies uniformly to setoid-valued and propositionally-valued orders.  That
generality is what the library's two motivating instances need: the congruence poset
`(Con 𝑨 , ≑ , ⊆)` of [Setoid.Congruences.Lattice][] carries an equivalence of *mutual
containment* rather than propositional equality, while a classical lattice carries
its meet order from [Classical.Properties.Lattice][].

(The standard library's `IsOrderIsomorphism`{.AgdaRecord} packages one map with
surjectivity instead of an explicit inverse; the two presentations are
interconvertible, and the inverse-pair form is the convenient one for transporting
structure.)

The record was introduced in [FLRP.Problem][], next to its first use, with a note
that it should migrate here once the group-theoretic side of the library needed it.
[Classical.Structures.Group.Congruences][] is that consumer — the correspondence
between normal subgroups and congruences is ordinary group theory, below the FLRP
tree — so the record now lives in `Order/` and [FLRP.Problem][] re-exports it.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Order.Iso where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Level            using ( Level ; _⊔_ )
open import Relation.Binary  using () renaming ( Rel to BinaryRel )
```
-->

#### The record

```agda
record OrderIso
  {a b ℓ₁ ℓ₂ m₁ m₂ : Level}
  {A : Type a} {B : Type b}
  (_≈₁_ : BinaryRel A ℓ₁) (_≤₁_ : BinaryRel A ℓ₂)
  (_≈₂_ : BinaryRel B m₁) (_≤₂_ : BinaryRel B m₂) : Type (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂ ⊔ m₁ ⊔ m₂) where
  field
    to         : A → B
    from       : B → A
    to-mono    : ∀ {x y} → x ≤₁ y → to x ≤₂ to y
    from-mono  : ∀ {u v} → u ≤₂ v → from u ≤₁ from v
    to∘from    : ∀ u → to (from u) ≈₂ u
    from∘to    : ∀ x → from (to x) ≈₁ x
```
