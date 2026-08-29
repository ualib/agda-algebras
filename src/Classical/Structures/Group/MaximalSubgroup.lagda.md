---
layout: default
file: "src/Classical/Structures/Group/MaximalSubgroup.lagda.md"
title: "Classical.Structures.Group.MaximalSubgroup module"
date: "2026-08-29"
author: "the agda-algebras development team"
---

### Maximal subgroups

This is the [Classical.Structures.Group.MaximalSubgroup][] module of the [Agda Universal Algebra Library][].

A **maximal subgroup** of `G` is a proper subgroup `H` such that no subgroup lies
strictly between `H` and `G`; equivalently, the interval `[H , G]` in the subgroup
lattice is the two-element chain.  Groups with a *core-free* maximal subgroup are
classically exactly the groups with a faithful primitive permutation action, which
is why the notion matters to the enforcement catalog of [FLRP.Reductions][]:
core-free interval enforceability via a two-element chain constrains precisely this
class of groups.

The definition is stated in the form the proofs consume, and that form deserves a
constructive health warning.  The field `classify`{.AgdaField} places every
intermediate subgroup at `H` or at `G` as a *disjunction*, and producing that
disjunction for an arbitrary equality-respecting predicate is oracle-strength data:
a subgroup can encode an arbitrary proposition in its membership predicate (for any
proposition `P`, the predicate `λ x → x ∈ H ⊎ P` respects equality and is closed
under the group operations), so `classify`{.AgdaField} applied to such a predicate
decides the proposition up to double negation.  Consequently no concrete group can
inhabit `IsMaximalSubgroup`{.AgdaRecord} in safe Agda; the record is a *named
classical hypothesis* in the sense of the FLRP assumption discipline, inhabited by
classical mathematics (where it is ordinary maximality) and consumed by theorems
that are honest about assuming it.  A decidable-membership sibling in the Layer-D
style of ADR-008, quantifying only over subgroups packaged with decision
procedures, would be constructible for concrete finite groups; it is deliberately
not defined here because no present consumer needs it.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.MaximalSubgroup where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Product     using  ( proj₁ )
open import Data.Sum.Base    using  ( _⊎_ )
open import Level            using  ( Level ; _⊔_ ) renaming ( suc to lsuc )
open import Relation.Nullary using  ( ¬_ )
open import Relation.Unary   using  ( Pred ; _∈_ ; _⊆_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Group.Basic            using  ( Group )
open import Classical.Structures.Group.Subgroups        using  ( IsSubgroup )
open import Classical.Structures.Group.SubgroupLattice  using  ( module GroupSublattice )
open import Setoid.Algebras.Basic                       using  ( 𝕌[_] )
```
-->

#### The maximality record

Throughout, `𝒢`{.AgdaBound} is a group and `ℓ₀`{.AgdaBound} the base level of its
subgroup lattice; subgroup predicates live at the resulting level `L`, exactly as
in [Classical.Structures.Group.MinimalNormal][].

`IsMaximalSubgroup`{.AgdaRecord} `H` bundles the three conditions: `H` is a
subgroup, it is proper (not every element lies in it, stated negatively because no
argument below needs a witness), and every subgroup between `H` and the whole group
is one of the two endpoints.  Given `H ⊆ K`, the first disjunct `K ⊆ H` says the
two predicates have the same extent, and the second says `K` is everything.

```agda
module MaximalSubgroup {α ρ : Level} (𝒢 : Group α ρ) (ℓ₀ : Level) where
  private
    G = 𝕌[ proj₁ 𝒢 ]

  open GroupSublattice 𝒢 ℓ₀  using  ( L )

  record IsMaximalSubgroup (H : Pred G L) : Type (α ⊔ ρ ⊔ lsuc L) where
    field
      isSubgroup  : IsSubgroup 𝒢 H
      proper      : ¬ (∀ x → x ∈ H)
      classify    : (K : Pred G L) → IsSubgroup 𝒢 K → H ⊆ K
                  → (K ⊆ H) ⊎ (∀ x → x ∈ K)

  open IsMaximalSubgroup public
```
