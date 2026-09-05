---
layout: default
file: "src/Classical/Structures/Lattice/FilterIdeal.lagda.md"
title: "Classical.Structures.Lattice.FilterIdeal module"
date: "2026-08-17"
author: "the agda-algebras development team"
---

### Principal filters, principal ideals, and their union

This is the [Classical.Structures.Lattice.FilterIdeal][] module of the [Agda Universal Algebra Library][].

For elements `a`{.AgdaBound} and `b`{.AgdaBound} of a lattice, the **principal
filter** `a ↑`{.AgdaFunction} is the up-set `{ x ∣ a ≤ x }` and the **principal
ideal** `b ↓`{.AgdaFunction} is the down-set `{ x ∣ x ≤ b }`, where `_≤_` is the
meet order of [Classical.Properties.Lattice][].  Each is a sublattice universe: a
filter is closed under meets because the meet of two upper bounds of
`a`{.AgdaBound} is again one (`∧-greatest`{.AgdaFunction}), and under joins
because `a ≤ x ≤ x ∨ y`; an ideal is closed dually.

The result this module exists for is the closure of the **union**
`a ↑ ∪ b ↓`{.AgdaFunction}: the union of a principal filter and a principal ideal
is again a sublattice universe, for *any* two elements `a`{.AgdaBound} and
`b`{.AgdaBound}.  The proof is one line in each direction, exactly as in the
manuscript (`docs/papers/fin-lat-rep/SmallLatticeReps.tex`
§ "Union of a filter and ideal"): if either argument lies in the ideal then so
does the meet, since `x ∧ y ≤ y ≤ b`; if either argument lies in the filter then
so does the join, since `a ≤ x ≤ x ∨ y`; and the remaining homogeneous cases are
the filter's meet-closure and the ideal's join-closure.

This is the order-theoretic half of Snow's filter-ideal lemma (Snow, *Algebra
Universalis* 43 (2000)); the congruence-theoretic half, saying that a sublattice
of a representable lattice with universe `a ↑ ∪ b ↓` is itself representable, is
[FLRP.Closure.FilterIdeal][], which proves the corresponding closure at the level
of decidable congruences and consumes the same case analysis.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Lattice.FilterIdeal where

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Product     using ( proj₁ )
open import Data.Sum.Base    using ( inj₁ ; inj₂ )
open import Level            using ( Level )
open import Relation.Unary   using ( Pred ; _∈_ ; _∪_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice        using ( module Lattice-Order )
open import Classical.Structures.Lattice.Basic  using ( Lattice ; module Lattice-Op )
open import Setoid.Algebras.Basic               using ( 𝕌[_] )

private variable α ρ : Level
```
-->

#### Principal filters and ideals

`FilterIdeal`{.AgdaModule} `𝑳` packages the two down/up-set formers and their
closure properties for a fixed lattice.

```agda
module FilterIdeal (𝑳 : Lattice α ρ) where
  private 𝑨 = proj₁ 𝑳

  open Lattice-Op 𝑳     using ( _∧_ ; _∨_ )
  open Lattice-Order 𝑳  using ( _≤_ ; ≤-trans ; ∧-lowerˡ ; ∧-lowerʳ ; ∧-greatest
                              ; ∨-upperˡ ; ∨-upperʳ ; ∨-least )

  -- The principal filter of a: all elements above a.
  _↑ : 𝕌[ 𝑨 ] → Pred 𝕌[ 𝑨 ] ρ
  a ↑ = λ x → a ≤ x

  -- The principal ideal of b: all elements below b.
  _↓ : 𝕌[ 𝑨 ] → Pred 𝕌[ 𝑨 ] ρ
  b ↓ = λ x → x ≤ b
```

A principal filter is closed under meets and joins, hence a sublattice universe;
the meet case is the universal property of the meet, and the join case is
transitivity through the left upper bound.

```agda
  -- A filter is closed under meets: the meet of two upper bounds of a is one.
  ↑-∧-closed : {a x y : 𝕌[ 𝑨 ]} → x ∈ a ↑ → y ∈ a ↑ → x ∧ y ∈ a ↑
  ↑-∧-closed = ∧-greatest

  -- A filter is closed under joins: a ≤ x ≤ x ∨ y.
  ↑-∨-closed : {a x y : 𝕌[ 𝑨 ]} → x ∈ a ↑ → x ∨ y ∈ a ↑
  ↑-∨-closed a≤x = ≤-trans a≤x ∨-upperˡ
```

Dually, a principal ideal is closed under joins and meets.

```agda
  -- An ideal is closed under joins: the join of two lower bounds of b is one.
  ↓-∨-closed : {b x y : 𝕌[ 𝑨 ]} → x ∈ b ↓ → y ∈ b ↓ → x ∨ y ∈ b ↓
  ↓-∨-closed = ∨-least

  -- An ideal is closed under meets: x ∧ y ≤ x ≤ b.
  ↓-∧-closed : {b x y : 𝕌[ 𝑨 ]} → x ∈ b ↓ → x ∧ y ∈ b ↓
  ↓-∧-closed x≤b = ≤-trans ∧-lowerˡ x≤b
```

#### The union of a filter and an ideal is a sublattice

The union `a ↑ ∪ b ↓` is closed under meet and join.  The four cases of each
closure proof are as in the manuscript: heterogeneous meets fall into the ideal
(`x ∧ y ≤ y ≤ b`), heterogeneous joins rise into the filter (`a ≤ x ≤ x ∨ y`),
and the homogeneous cases are the closure properties above.

```agda
  module _ (a b : 𝕌[ 𝑨 ]) where

    -- The union of the principal filter of a and the principal ideal of b.
    filterIdealUnion : Pred 𝕌[ 𝑨 ] ρ
    filterIdealUnion = a ↑ ∪ b ↓

    -- The union is closed under meets.
    ∪-∧-closed :  {x y : 𝕌[ 𝑨 ]}
      →           x ∈ filterIdealUnion → y ∈ filterIdealUnion
      →           x ∧ y ∈ filterIdealUnion
    ∪-∧-closed (inj₁ a≤x)  (inj₁ a≤y)  = inj₁ (↑-∧-closed a≤x a≤y)
    ∪-∧-closed (inj₁ _)    (inj₂ y≤b)  = inj₂ (≤-trans ∧-lowerʳ y≤b)
    ∪-∧-closed (inj₂ x≤b)  (inj₁ _)    = inj₂ (↓-∧-closed x≤b)
    ∪-∧-closed (inj₂ x≤b)  (inj₂ _)    = inj₂ (↓-∧-closed x≤b)

    -- The union is closed under joins.
    ∪-∨-closed :  {x y : 𝕌[ 𝑨 ]}
      →           x ∈ filterIdealUnion → y ∈ filterIdealUnion
      →           x ∨ y ∈ filterIdealUnion
    ∪-∨-closed (inj₁ a≤x)  (inj₁ _)    = inj₁ (↑-∨-closed a≤x)
    ∪-∨-closed (inj₁ a≤x)  (inj₂ _)    = inj₁ (↑-∨-closed a≤x)
    ∪-∨-closed (inj₂ _)    (inj₁ a≤y)  = inj₁ (≤-trans a≤y ∨-upperʳ)
    ∪-∨-closed (inj₂ x≤b)  (inj₂ y≤b)  = inj₂ (↓-∨-closed x≤b y≤b)
```

--------------------------------------
