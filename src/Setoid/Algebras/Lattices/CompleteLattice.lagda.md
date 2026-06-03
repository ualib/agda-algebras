---
layout: default
title : "Setoid.Algebras.Lattices.CompleteLattice module (The Agda Universal Algebra Library)"
date : "2026-06-02"
author: "agda-algebras development team"
---

### Complete Lattices

This is the [Setoid.Algebras.Lattices.CompleteLattice][] module of the [Agda Universal Algebra Library][].

The standard library provides order-theoretic semilattices, lattices, and bounded
lattices, but no *complete* lattice, so we define one here.

A **complete lattice** is a partially ordered set in which every family of elements
(indexed by a type at a fixed level `ι`) has a supremum and an infimum.

Although this notion is pure order theory, complete lattices are pervasive in
universal algebra — the congruence lattice
([Setoid.Algebras.Congruences.CompleteLattice][]) and the subalgebra lattice are the
motivating instances — so we keep the definition in the `Algebras` tree rather than
relegating it to `Classical`.  Every supremum/infimum is required to exist only for
`ι`-small index types, the customary predicative reading of "complete."

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Algebras.Lattices.CompleteLattice where

open import Agda.Primitive   using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Level            using ( Level ; _⊔_ ; suc )
open import Relation.Binary  using ( IsPartialOrder ) renaming ( Rel to BinRel )
```

`CompleteLattice c ℓ₁ ℓ₂ ι` is a carrier at level `c` with an equality at level `ℓ₁`
and a partial order at level `ℓ₂`, such that every `ι`-indexed family has a least
upper bound `⨆` and a greatest lower bound `⨅`.

```agda
record CompleteLattice (c ℓ₁ ℓ₂ ι : Level) : Type (suc (c ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ι)) where
  field
    Carrier         : Type c
    _≈_             : BinRel Carrier ℓ₁
    _≤_             : BinRel Carrier ℓ₂
    isPartialOrder  : IsPartialOrder _≈_ _≤_

    -- Infinitary supremum and infimum of an ι-indexed family.
    ⨆ : {I : Type ι} → (I → Carrier) → Carrier
    ⨅ : {I : Type ι} → (I → Carrier) → Carrier

    -- ⨆ f is the least upper bound of the family f.
    ⨆-upper  : {I : Type ι} (f : I → Carrier) (i : I) → f i ≤ ⨆ f
    ⨆-least  : {I : Type ι} (f : I → Carrier) (x : Carrier) → (∀ i → f i ≤ x) → ⨆ f ≤ x

    -- ⨅ f is the greatest lower bound of the family f.
    ⨅-lower     : {I : Type ι} (f : I → Carrier) (i : I) → ⨅ f ≤ f i
    ⨅-greatest  : {I : Type ι} (f : I → Carrier) (x : Carrier) → (∀ i → x ≤ f i) → x ≤ ⨅ f
```

--------------------------------------

<span style="float:left;">[↑ Setoid.Algebras.Lattices](Setoid.Algebras.Lattices.html)</span>
<span style="float:right;">[Setoid.Algebras.Congruences.CompleteLattice →](Setoid.Algebras.Congruences.CompleteLattice.html)</span>

{% include UALib.Links.md %}
