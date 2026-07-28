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
open import Function         using ( _∘_ )
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

#### Composition

Order isomorphisms compose.  The round trips of the composite pass the inner
round trip through the outer maps, which is sound only *up to the middle
equivalence* — so composition asks for two congruence witnesses (the second
map's `to` and the first map's `from` respect the middle equivalence) and for
transitivity of the two end equivalences.  These are not derivable from the
raw relations, but every instance has them: for setoid-valued orders they are
the setoid laws, and for containment-style orders (congruences, intervals,
partitions) they are monotonicity applied to the two directions of the
equivalence.  Nothing is assumed of the middle relations beyond what the two
isomorphisms already state.

```agda
module _
  {a b c ℓ₁ ℓ₂ m₁ m₂ n₁ n₂ : Level}
  {A : Type a} {B : Type b} {C : Type c}
  {_≈₁_ : BinaryRel A ℓ₁} {_≤₁_ : BinaryRel A ℓ₂}
  {_≈₂_ : BinaryRel B m₁} {_≤₂_ : BinaryRel B m₂}
  {_≈₃_ : BinaryRel C n₁} {_≤₃_ : BinaryRel C n₂}
  where

  -- Composition of order isomorphisms, given the two congruence witnesses at
  -- the middle equivalence and transitivity at the ends.
  OrderIso-trans :
      (F : OrderIso _≈₁_ _≤₁_ _≈₂_ _≤₂_) (G : OrderIso _≈₂_ _≤₂_ _≈₃_ _≤₃_)
    → (∀ {x y} → x ≈₂ y → OrderIso.to G x ≈₃ OrderIso.to G y)
    → (∀ {x y} → x ≈₂ y → OrderIso.from F x ≈₁ OrderIso.from F y)
    → (∀ {x y z} → x ≈₁ y → y ≈₁ z → x ≈₁ z)
    → (∀ {x y z} → x ≈₃ y → y ≈₃ z → x ≈₃ z)
    → OrderIso _≈₁_ _≤₁_ _≈₃_ _≤₃_
  OrderIso-trans F G G-to-cong F-from-cong ≈₁-trans ≈₃-trans = record
    { to         = G.to ∘ F.to
    ; from       = F.from ∘ G.from
    ; to-mono    = G.to-mono ∘ F.to-mono
    ; from-mono  = F.from-mono ∘ G.from-mono
    ; to∘from    = λ u → ≈₃-trans (G-to-cong (F.to∘from (G.from u))) (G.to∘from u)
    ; from∘to    = λ x → ≈₁-trans (F-from-cong (G.from∘to (F.to x))) (F.from∘to x)
    }
    where
    module F = OrderIso F
    module G = OrderIso G
```

--------------------------------------
