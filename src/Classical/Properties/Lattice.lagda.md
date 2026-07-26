---
layout: default
file: "src/Classical/Properties/Lattice.lagda.md"
title: "Classical.Properties.Lattice module"
date: "2026-05-28"
author: "the agda-algebras development team"
---

### The meet-join / order-theoretic view of a lattice {#classical-properties-lattice}

This is the [Classical.Properties.Lattice][] module of the [Agda Universal Algebra Library][].

The algebraic and order-theoretic presentations of a lattice are equivalent.
This module proves the *object-level* half of that equivalence: given
a `Lattice α ρ` — that is, the algebraic data of meet, join, and the eight
equations — we construct the partial order `x ≤ y := x ∧ y ≈ x` and show that
`_∧_` and `_∨_` are the binary meet and join with respect to it.

This is the first module in `Classical/Properties/`.  The directory is a by-concern
parallel of `Classical/Structures/`, `Classical/Bundles/`, etc., for *derived*
results about classical structures — results that are theorems *about* a fixed
inhabitant of one of those structures, not part of its definition.  Future
inhabitants include, for example, uniqueness of inverses in Group and `0 · x ≈ 0`
in Ring.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Properties.Lattice where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -----------------------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Properties                    using ( _≟_ ; all? )
open import Data.Nat.Base                          using ( ℕ )
open import Data.Product                           using ( proj₁ ; _×_ ; Σ-syntax )
open import Data.Sum.Base                          using ( _⊎_ )
open import Level                                  using ( Level ; _⊔_ )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; _≢_ )
open import Relation.Nullary.Decidable.Core        using ( Dec ; ¬? ; _×-dec_ ; _→-dec_ ; _⊎-dec_ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library --------------------------------
open import Classical.Structures.Lattice.Basic  using ( Lattice ; module Lattice-Op )
open import Setoid.Algebras.Basic               using ( 𝔻[_] ; 𝕌[_] )

private variable α ρ : Level
```
-->

#### The `Lattice-Order` module {#lattice-order}

```agda
module Lattice-Order {α ρ : Level} (𝑳 : Lattice α ρ) where
  private 𝑨 = proj₁ 𝑳
  open Setoid 𝔻[ 𝑨 ]
  open Lattice-Op 𝑳
  open SetoidReasoning 𝔻[ 𝑨 ]
```

**The induced order**.

`x ≤ y` is `x ∧ y ≈ x` (the meet-form characterization).
The join-form `x ∨ y ≈ y` is proved iff-equivalent below.

```agda
  infix 4 _≤_
  _≤_ : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → Type ρ
  x ≤ y = x ∧ y ≈ x
```

The dual order characterization `x ≤ y ⇔ x ∨ y ≈ y` is proved as the connecting
lemma.  The partial-order properties and the GLB properties use only associativity,
commutativity, and idempotency; the join upper-bound clauses use absorption directly,
and the join leastness proof routes through the connecting lemma.

**Connecting lemma: meet-form and join-form agree**.

Forward direction uses the second absorption law (in its `absorbʳ-law` shape:
`(y ∧ x) ∨ y ≈ y`); backward direction uses the first.


```agda
  ≤-via-∨ : ∀ {x y} → x ≤ y → x ∨ y ≈ y
  ≤-via-∨ {x} {y} x≤y = begin
    x ∨ y         ≈˘⟨ ∨-cong x≤y refl ⟩
    (x ∧ y) ∨ y   ≈⟨ ∨-cong ∧-comm-law refl ⟩
    (y ∧ x) ∨ y   ≈⟨ absorbʳ-law ⟩
    y             ∎

  ≤-from-∨ : ∀ {x y} → x ∨ y ≈ y → x ≤ y
  ≤-from-∨ {x} {y} x∨y≈y = begin
    x ∧ y         ≈˘⟨ ∧-cong refl x∨y≈y ⟩
    x ∧ (x ∨ y)   ≈⟨ absorbˡ-law ⟩
    x             ∎
```

**Partial order modulo `≈`**.

Reflexivity is idempotency, transitivity uses associativity, antisymmetry uses
commutativity, and the `≈`-respect lemmas use binary congruence.

```agda
  ≤-refl : ∀ {x} → x ≤ x
  ≤-refl = ∧-idem-law

  ≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
  ≤-trans {x} {y} {z} x≤y y≤z = begin
    x ∧ z         ≈˘⟨ ∧-cong x≤y refl ⟩
    (x ∧ y) ∧ z   ≈⟨ ∧-assoc-law ⟩
    x ∧ (y ∧ z)   ≈⟨ ∧-cong refl y≤z ⟩
    x ∧ y         ≈⟨ x≤y ⟩
    x             ∎

  ≤-antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≈ y
  ≤-antisym {x} {y} x≤y y≤x = begin
    x       ≈˘⟨ x≤y ⟩
    x ∧ y   ≈⟨ ∧-comm-law ⟩
    y ∧ x   ≈⟨ y≤x ⟩
    y       ∎

  ≤-respˡ-≈ : ∀ {x x' y} → x ≈ x' → x ≤ y → x' ≤ y
  ≤-respˡ-≈ {x} {x'} {y} x≈x' x≤y = begin
    x' ∧ y   ≈˘⟨ ∧-cong x≈x' refl ⟩
    x ∧ y    ≈⟨ x≤y ⟩
    x        ≈⟨ x≈x' ⟩
    x'       ∎

  ≤-respʳ-≈ : ∀ {x y y'} → y ≈ y' → x ≤ y → x ≤ y'
  ≤-respʳ-≈ {x} {y} {y'} y≈y' x≤y = begin
    x ∧ y'   ≈˘⟨ ∧-cong refl y≈y' ⟩
    x ∧ y    ≈⟨ x≤y ⟩
    x        ∎

  -- ≈-equal elements are ≤-comparable (the `reflexive` field of the preorder).
  ≤-reflexive : ∀ {x y} → x ≈ y → x ≤ y
  ≤-reflexive {x} {y} x≈y = begin
    x ∧ y   ≈˘⟨ ∧-cong refl x≈y ⟩
    x ∧ x   ≈⟨ ∧-idem-law ⟩
    x       ∎
```

**`_∧_` is the binary meet**.

The two lower-bound clauses and the universal property, together with the
partial-order facts above, say that `x ∧ y` is the greatest lower bound of `x` and
`y` with respect to `_≤_`.

```agda
  ∧-lowerˡ : ∀ {x y} → (x ∧ y) ≤ x
  ∧-lowerˡ {x} {y} = begin
    (x ∧ y) ∧ x   ≈⟨ ∧-comm-law ⟩
    x ∧ (x ∧ y)   ≈˘⟨ ∧-assoc-law ⟩
    (x ∧ x) ∧ y   ≈⟨ ∧-cong ∧-idem-law refl ⟩
    x ∧ y         ∎

  ∧-lowerʳ : ∀ {x y} → (x ∧ y) ≤ y
  ∧-lowerʳ {x} {y} = begin
    (x ∧ y) ∧ y   ≈⟨ ∧-assoc-law ⟩
    x ∧ (y ∧ y)   ≈⟨ ∧-cong refl ∧-idem-law ⟩
    x ∧ y         ∎

  ∧-greatest : ∀ {x y z} → z ≤ x → z ≤ y → z ≤ (x ∧ y)
  ∧-greatest {x} {y} {z} z≤x z≤y = begin
    z ∧ (x ∧ y)   ≈˘⟨ ∧-assoc-law ⟩
    (z ∧ x) ∧ y   ≈⟨ ∧-cong z≤x refl ⟩
    z ∧ y         ≈⟨ z≤y ⟩
    z             ∎
```

**`_∨_` is the binary join**.  Dually: `x ∨ y` is the least upper bound of `x`
and `y`.  The two upper-bound clauses use absorption directly; the universal
property is proved through the join-form characterization to avoid going
through absorption twice.

```agda
  ∨-upperˡ : ∀ {x y} → x ≤ (x ∨ y)
  ∨-upperˡ = absorbˡ-law

  ∨-upperʳ : ∀ {x y} → y ≤ (x ∨ y)
  ∨-upperʳ {x} {y} = begin
    y ∧ (x ∨ y)   ≈⟨ ∧-cong refl ∨-comm-law ⟩
    y ∧ (y ∨ x)   ≈⟨ absorbˡ-law ⟩
    y             ∎

  ∨-least : ∀ {x y z} → x ≤ z → y ≤ z → (x ∨ y) ≤ z
  ∨-least {x} {y} {z} x≤z y≤z = ≤-from-∨ (begin
    (x ∨ y) ∨ z   ≈⟨ ∨-assoc-law ⟩
    x ∨ (y ∨ z)   ≈⟨ ∨-cong refl (≤-via-∨ y≤z) ⟩
    x ∨ z         ≈⟨ ≤-via-∨ x≤z ⟩
    z             ∎)
```

**Extrema**.  `IsTop t` says `t` is a greatest element of the meet order, and
`IsBot b` that `b` is a least one.  An arbitrary lattice need not have either; the
predicates state the universal property of a *chosen* extremum, and by antisymmetry
any two choices are `≈`-equal.  Constructions that glue lattices at their ends — the
ordinal sum of [Classical.Structures.Lattice.OrdinalSum][] — consume exactly this
data.

```agda
  -- t is a top (greatest) element of the meet order.
  IsTop : 𝕌[ 𝑨 ] → Type (α ⊔ ρ)
  IsTop t = ∀ x → x ≤ t

  -- b is a bottom (least) element of the meet order.
  IsBot : 𝕌[ 𝑨 ] → Type (α ⊔ ρ)
  IsBot b = ∀ x → b ≤ x

  -- Tops are unique up to ≈, by antisymmetry; likewise bottoms.
  top-unique : ∀ {t t'} → IsTop t → IsTop t' → t ≈ t'
  top-unique {t} {t'} pt pt' = ≤-antisym (pt' t) (pt t')

  bot-unique : ∀ {b b'} → IsBot b → IsBot b' → b ≈ b'
  bot-unique {b} {b'} pb pb' = ≤-antisym (pb b') (pb' b)
```

#### Chosen extrema, packaged

`TopOf 𝑳` is the type of chosen tops of `𝑳`: an element paired with its
universal property; `BotOf 𝑳` likewise for bottoms.  These are the arguments a
construction takes when it needs a *specific* extremum (again, see the ordinal sum),
packaged as Σ-types per the library's Σ-first discipline.

```agda
TopOf : Lattice α ρ → Type (α ⊔ ρ)
TopOf 𝑳 = Σ[ t ∈ 𝕌[ proj₁ 𝑳 ] ] Lattice-Order.IsTop 𝑳 t

BotOf : Lattice α ρ → Type (α ⊔ ρ)
BotOf 𝑳 = Σ[ b ∈ 𝕌[ proj₁ 𝑳 ] ] Lattice-Order.IsBot 𝑳 b
```

#### The decidable meet order and its atoms {#finite-order}

`FiniteOrder _∧_` packages the meet order `a ≤ b := a ∧ b ≡ a` over a finite carrier
together with its decision procedure.  Fixing a bottom `⊥` and top `⊤` (submodule
`Bounded`) it provides the `atom`/`coatom` predicates and their deciders.  This is
the finite, decidable counterpart of the setoid-level `Lattice-Order._≤_` above, and
is what the finite lattice examples reuse.

```agda
module FiniteOrder {n : ℕ} (_∧_ : Fin n → Fin n → Fin n) where
  infix 4 _≤_ _≤?_

  _≤_ : Fin n → Fin n → Type
  a ≤ b = a ∧ b ≡ a

  _≤?_ : (a b : Fin n) → Dec (a ≤ b)
  a ≤? b = a ∧ b ≟ a

  module Bounded (⊥ ⊤ : Fin n) where

    -- a is an atom: a ≠ ⊥, with nothing strictly between ⊥ and a.
    atom : Fin n → Type
    atom a = (a ≢ ⊥) × (∀ b → b ≤ a → (b ≡ ⊥) ⊎ (b ≡ a))

    -- a is a coatom: a ≠ ⊤, with nothing strictly between a and ⊤.
    coatom : Fin n → Type
    coatom a = (a ≢ ⊤) × (∀ b → a ≤ b → (b ≡ a) ⊎ (b ≡ ⊤))

    atom? : (a : Fin n) → Dec (atom a)
    atom? a = ¬? (a ≟ ⊥) ×-dec all? (λ b → (b ≤? a) →-dec ((b ≟ ⊥) ⊎-dec (b ≟ a)))

    coatom? : (a : Fin n) → Dec (coatom a)
    coatom? a = ¬? (a ≟ ⊤) ×-dec all? (λ b → (a ≤? b) →-dec ((b ≟ a) ⊎-dec (b ≟ ⊤)))
```
