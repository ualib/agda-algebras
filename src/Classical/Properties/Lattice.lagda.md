---
layout: default
file: "src/Classical/Properties/Lattice.lagda.md"
title: "Classical.Properties.Lattice module"
date: "2026-05-28"
author: "the agda-algebras development team"
---

### <a id="classical-properties-lattice">The meet-join / order-theoretic view of a lattice</a>

This is the [Classical.Properties.Lattice][] module of the [Agda Universal Algebra Library][].

The acceptance criterion of [M3-7](https://github.com/ualib/agda-algebras/issues/264)
asks for the equivalence of the algebraic and order-theoretic presentations of a
lattice.  This module proves the *object-level* half of that equivalence: given
a `Lattice α ρ` — that is, the algebraic data of meet, join, and the eight
equations — we construct the partial order `x ≤ y := x ∧ y ≈ x` and show that
`_∧_` and `_∨_` are the binary meet and join with respect to it.

The dual order characterization `x ≤ y ⇔ x ∨ y ≈ y` is proved as the connecting
lemma; absorption is used in exactly that one place.  The partial-order
properties (reflexivity, transitivity, antisymmetry, congruence in `≈`) and the
GLB/LUB properties (universal property of meet and join with respect to `_≤_`)
follow from associativity, commutativity, and idempotency together with the
connecting lemma — assoc/comm/idem alone do not suffice for the LUB direction.

This is the first module in `Classical/Properties/`.  The directory is a
by-concern parallel of `Classical/Structures/`, `Classical/Bundles/`, etc., for
*derived* results about classical structures — results that are theorems
*about* a fixed inhabitant of one of those structures, not part of its
definition.  Future inhabitants include, for example, uniqueness of inverses in
Group and `0 · x ≈ 0` in Ring.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Properties.Lattice where

open import Agda.Primitive                           using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -----------------------------------------
open import Data.Product                             using ( proj₁ )
open import Level                                    using ( Level ; _⊔_ )
open import Relation.Binary                          using ( Setoid )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library --------------------------------
open import Classical.Signatures.Lattice             using ( Sig-Lattice )
open import Classical.Structures.Lattice             using ( Lattice ; module Lattice-Op )
open import Setoid.Algebras.Basic {𝑆 = Sig-Lattice}  using ( 𝔻[_] ; 𝕌[_] )

private variable α ρ : Level
```

#### <a id="lattice-order">The `Lattice-Order` module</a>

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
backward direction uses the first.  This is the *only* place absorption is
invoked in this module — all the partial-order and GLB results below need only
associativity, commutativity, and idempotency.

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

--------------------------------------

{% include UALib.Links.md %}
