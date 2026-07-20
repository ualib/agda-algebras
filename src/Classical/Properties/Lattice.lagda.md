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

The dual order characterization `x ≤ y ⇔ x ∨ y ≈ y` is proved as the connecting
lemma.  The partial-order properties and the GLB properties use only
associativity, commutativity, and idempotency; the join upper-bound clauses use
absorption directly, and the join leastness proof routes through the connecting
lemma.

This is the first module in `Classical/Properties/`.  The directory is a
by-concern parallel of `Classical/Structures/`, `Classical/Bundles/`, etc., for
*derived* results about classical structures — results that are theorems
*about* a fixed inhabitant of one of those structures, not part of its
definition.  Future inhabitants include, for example, uniqueness of inverses in
Group and `0 · x ≈ 0` in Ring.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Properties.Lattice where

open import Agda.Primitive                           using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -----------------------------------------
open import Data.Fin.Base                            using ( Fin )
open import Data.Fin.Properties                      using ( _≟_ ; all? )
open import Data.Nat.Base                            using ( ℕ )
open import Data.Product                             using ( proj₁ ; _×_ )
open import Data.Sum.Base                            using ( _⊎_ )
open import Level                                    using ( Level )
open import Relation.Binary                          using ( Setoid )
open import Relation.Binary.PropositionalEquality    using ( _≡_ ; _≢_ )
open import Relation.Nullary.Decidable.Core          using ( Dec ; ¬? ; _×-dec_ ; _→-dec_ ; _⊎-dec_ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library --------------------------------
open import Classical.Signatures.Lattice             using ( Sig-Lattice )
open import Classical.Structures.Lattice             using ( Lattice ; module Lattice-Op )
open import Setoid.Algebras.Basic  using ( 𝔻[_] ; 𝕌[_] )

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

**The induced order.**  `x ≤ y` is `x ∧ y ≈ x` (the meet-form characterization).
The join-form `x ∨ y ≈ y` is proved iff-equivalent below.

```agda
  infix 4 _≤_
  _≤_ : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → Type ρ
  x ≤ y = x ∧ y ≈ x
```

**Connecting lemma: meet-form and join-form agree.**  Forward direction uses
the second absorption law (in its `absorbʳ-law` shape: `(y ∧ x) ∨ y ≈ y`);
backward direction uses the first.  The partial-order and GLB results below need
only associativity, commutativity, and idempotency; the join upper-bound clauses
use absorption directly.

```agda
  ≤-via-∨ : ∀ {x y} → x ≤ y → x ∨ y ≈ y
  ≤-via-∨ {x} {y} x≤y = begin
    x ∨ y         ≈⟨ ∨-cong (sym x≤y) refl ⟩
    (x ∧ y) ∨ y   ≈⟨ ∨-cong (∧-comm-law x y) refl ⟩
    (y ∧ x) ∨ y   ≈⟨ absorbʳ-law y x ⟩
    y             ∎

  ≤-from-∨ : ∀ {x y} → x ∨ y ≈ y → x ≤ y
  ≤-from-∨ {x} {y} x∨y≈y = begin
    x ∧ y         ≈⟨ ∧-cong refl (sym x∨y≈y) ⟩
    x ∧ (x ∨ y)   ≈⟨ absorbˡ-law x y ⟩
    x             ∎
```

**Partial order modulo `≈`.**  Reflexivity is idempotency, transitivity uses
associativity, antisymmetry uses commutativity, and the `≈`-respect lemmas use
binary congruence.

```agda
  ≤-refl : ∀ {x} → x ≤ x
  ≤-refl {x} = ∧-idem-law x

  ≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
  ≤-trans {x} {y} {z} x≤y y≤z = begin
    x ∧ z         ≈⟨ ∧-cong (sym x≤y) refl ⟩
    (x ∧ y) ∧ z   ≈⟨ ∧-assoc-law x y z ⟩
    x ∧ (y ∧ z)   ≈⟨ ∧-cong refl y≤z ⟩
    x ∧ y         ≈⟨ x≤y ⟩
    x             ∎

  ≤-antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≈ y
  ≤-antisym {x} {y} x≤y y≤x = begin
    x       ≈⟨ sym x≤y ⟩
    x ∧ y   ≈⟨ ∧-comm-law x y ⟩
    y ∧ x   ≈⟨ y≤x ⟩
    y       ∎

  ≤-respˡ-≈ : ∀ {x x' y} → x ≈ x' → x ≤ y → x' ≤ y
  ≤-respˡ-≈ {x} {x'} {y} x≈x' x≤y = begin
    x' ∧ y   ≈⟨ ∧-cong (sym x≈x') refl ⟩
    x ∧ y    ≈⟨ x≤y ⟩
    x        ≈⟨ x≈x' ⟩
    x'       ∎

  ≤-respʳ-≈ : ∀ {x y y'} → y ≈ y' → x ≤ y → x ≤ y'
  ≤-respʳ-≈ {x} {y} {y'} y≈y' x≤y = begin
    x ∧ y'   ≈⟨ ∧-cong refl (sym y≈y') ⟩
    x ∧ y    ≈⟨ x≤y ⟩
    x        ∎
```

**`_∧_` is the binary meet.**  The two lower-bound clauses and the universal
property — together with the partial-order facts above — say that `x ∧ y` is
the greatest lower bound of `x` and `y` with respect to `_≤_`.

```agda
  ∧-lowerˡ : ∀ x y → (x ∧ y) ≤ x
  ∧-lowerˡ x y = begin
    (x ∧ y) ∧ x   ≈⟨ ∧-comm-law (x ∧ y) x ⟩
    x ∧ (x ∧ y)   ≈⟨ sym (∧-assoc-law x x y) ⟩
    (x ∧ x) ∧ y   ≈⟨ ∧-cong (∧-idem-law x) refl ⟩
    x ∧ y         ∎

  ∧-lowerʳ : ∀ x y → (x ∧ y) ≤ y
  ∧-lowerʳ x y = begin
    (x ∧ y) ∧ y   ≈⟨ ∧-assoc-law x y y ⟩
    x ∧ (y ∧ y)   ≈⟨ ∧-cong refl (∧-idem-law y) ⟩
    x ∧ y         ∎

  ∧-greatest : ∀ {x y z} → z ≤ x → z ≤ y → z ≤ (x ∧ y)
  ∧-greatest {x} {y} {z} z≤x z≤y = begin
    z ∧ (x ∧ y)   ≈⟨ sym (∧-assoc-law z x y) ⟩
    (z ∧ x) ∧ y   ≈⟨ ∧-cong z≤x refl ⟩
    z ∧ y         ≈⟨ z≤y ⟩
    z             ∎
```

**`_∨_` is the binary join.**  Dually: `x ∨ y` is the least upper bound of `x`
and `y`.  The two upper-bound clauses use absorption directly; the universal
property is proved through the join-form characterization to avoid going
through absorption twice.

```agda
  ∨-upperˡ : ∀ x y → x ≤ (x ∨ y)
  ∨-upperˡ x y = absorbˡ-law x y

  ∨-upperʳ : ∀ x y → y ≤ (x ∨ y)
  ∨-upperʳ x y = begin
    y ∧ (x ∨ y)   ≈⟨ ∧-cong refl (∨-comm-law x y) ⟩
    y ∧ (y ∨ x)   ≈⟨ absorbˡ-law y x ⟩
    y             ∎

  ∨-least : ∀ {x y z} → x ≤ z → y ≤ z → (x ∨ y) ≤ z
  ∨-least {x} {y} {z} x≤z y≤z = ≤-from-∨ (begin
    (x ∨ y) ∨ z   ≈⟨ ∨-assoc-law x y z ⟩
    x ∨ (y ∨ z)   ≈⟨ ∨-cong refl (≤-via-∨ y≤z) ⟩
    x ∨ z         ≈⟨ ≤-via-∨ x≤z ⟩
    z             ∎)
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
  a ≤? b = (a ∧ b) ≟ a

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
