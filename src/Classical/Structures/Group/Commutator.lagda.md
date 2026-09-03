---
layout: default
file: "src/Classical/Structures/Group/Commutator.lagda.md"
title: "Classical.Structures.Group.Commutator module"
date: "2026-09-02"
author: "the agda-algebras development team"
---

### Commutators

This is the [Classical.Structures.Group.Commutator][] module of the [Agda Universal Algebra Library][].

For elements `x` and `y` of a group, the **commutator** `comm x y = x ∙ y ∙ x ⁻¹ ∙ y ⁻¹` measures the failure of `x` and `y` to commute: it is the identity exactly when `x ∙ y ≈ y ∙ x`.  This module defines the commutator and the commuting relation, and proves the small algebra the normal-subgroup structure theory of powers consumes:

+  `Commutes`{.AgdaFunction} and `comm`{.AgdaFunction}, with their congruence lemmas;
+  the two absorption laws: a commutator with the identity in either slot is the identity;
+  the equivalence between `comm x y ≈ ε` and `Commutes x y`, in both directions.

The absorption laws are the engine of the support-shrinking argument for subgroups of a power above the diagonal: a commutator of two tuples vanishes at every coordinate where *either* tuple vanishes, so iterated commutators cut a member's support down to a prescribed block while the equivalence keeps a designated coordinate away from the identity.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.Commutator where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Product     using  ( proj₁ )
open import Level            using  ( Level )
open import Relation.Binary  using  ( Setoid )
open import Relation.Nullary using  ( ¬_ )

import Algebra.Properties.Group as GroupProperties
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Bundles.Group           using  ( ⟨_⟩ᵍᵖ )
open import Classical.Structures.Group.Basic  using  ( Group ; module Group-Op )
open import Setoid.Algebras.Basic             using  ( 𝕌[_] ; 𝔻[_] )
```
-->

#### The commutator and the commuting relation

`Commutator`{.AgdaModule}` 𝒢` packages the two notions and their algebra for a fixed group.

```agda
module Commutator {α ρ : Level} (𝒢 : Group α ρ) where

  private
    𝑮 = proj₁ 𝒢
    G = 𝕌[ 𝑮 ]

  open Setoid 𝔻[ 𝑮 ]            using  ( _≈_ )
                                renaming  ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open SetoidReasoning 𝔻[ 𝑮 ]
  open Group-Op 𝒢               using  ( _∙_ ; ε ; _⁻¹ ; ∙-cong ; ⁻¹-cong ; assoc-law
                                        ; idˡ-law ; idʳ-law ; invˡ-law ; invʳ-law )
  open GroupProperties ⟨ 𝒢 ⟩ᵍᵖ  using  ( ε⁻¹≈ε )
```

**The commuting relation**: `x` and `y` commute when the two products agree.

```agda
  -- The commuting relation.
  Commutes : G → G → Type ρ
  Commutes x y = x ∙ y ≈ y ∙ x
```

The relation is a congruence in each slot separately; the right-slot form is the one the finite searches below the diagonal transport along an enumeration.

```agda
  -- Commuting is preserved by ≈ in the right slot.
  Commutes-congʳ : ∀ {x y y'} → y ≈ y' → Commutes x y → Commutes x y'
  Commutes-congʳ {x} {y} {y'} e c = begin
    x ∙ y'  ≈˘⟨ ∙-cong ≈refl e ⟩
    x ∙ y   ≈⟨ c ⟩
    y ∙ x   ≈⟨ ∙-cong e ≈refl ⟩
    y' ∙ x  ∎
```

**The commutator**, in the left-normed convention `x ∙ y ∙ x ⁻¹ ∙ y ⁻¹`.

```agda
  -- The commutator of two elements.
  comm : G → G → G
  comm x y = x ∙ y ∙ x ⁻¹ ∙ y ⁻¹
```

The commutator is a congruence in both slots at once, by the congruences of the two group operations.

```agda
  -- The commutator respects ≈ in both slots.
  comm-cong : ∀ {x x' y y'} → x ≈ x' → y ≈ y' → comm x y ≈ comm x' y'
  comm-cong ex ey = ∙-cong (∙-cong (∙-cong ex ey) (⁻¹-cong ex)) (⁻¹-cong ey)
```

#### The absorption laws

A commutator with the identity in the left slot collapses: the two `x`-factors become `ε` and `ε ⁻¹`, and what remains is `y ∙ y ⁻¹`.

```agda
  -- A commutator with the identity on the left is the identity.
  comm-εˡ : ∀ {x} y → x ≈ ε → comm x y ≈ ε
  comm-εˡ {x} y x≈ε = begin
    x ∙ y ∙ x ⁻¹ ∙ y ⁻¹  ≈⟨ ∙-cong (∙-cong (∙-cong x≈ε ≈refl) (⁻¹-cong x≈ε)) ≈refl ⟩
    ε ∙ y ∙ ε ⁻¹ ∙ y ⁻¹  ≈⟨ ∙-cong (∙-cong (idˡ-law y) ε⁻¹≈ε) ≈refl ⟩
    y ∙ ε ∙ y ⁻¹         ≈⟨ ∙-cong (idʳ-law y) ≈refl ⟩
    y ∙ y ⁻¹             ≈⟨ invʳ-law y ⟩
    ε                    ∎
```

Symmetrically for the right slot, where what remains is `x ∙ x ⁻¹`.

```agda
  -- A commutator with the identity on the right is the identity.
  comm-εʳ : ∀ x {y} → y ≈ ε → comm x y ≈ ε
  comm-εʳ x {y} y≈ε = begin
    x ∙ y ∙ x ⁻¹ ∙ y ⁻¹  ≈⟨ ∙-cong (∙-cong (∙-cong ≈refl y≈ε) ≈refl) (⁻¹-cong y≈ε) ⟩
    x ∙ ε ∙ x ⁻¹ ∙ ε ⁻¹  ≈⟨ ∙-cong (∙-cong (idʳ-law x) ≈refl) ε⁻¹≈ε ⟩
    x ∙ x ⁻¹ ∙ ε         ≈⟨ idʳ-law (x ∙ x ⁻¹) ⟩
    x ∙ x ⁻¹             ≈⟨ invʳ-law x ⟩
    ε                    ∎
```

#### The commutator detects commuting

Multiplying the commutator by `y ∙ x` on the right telescopes back to `x ∙ y`, so a trivial commutator forces the products to agree.

```agda
  -- A trivial commutator means the elements commute.
  comm≈ε→commutes : ∀ x y → comm x y ≈ ε → Commutes x y
  comm≈ε→commutes x y h = begin
    x ∙ y                              ≈˘⟨ idʳ-law (x ∙ y) ⟩
    x ∙ y ∙ ε                          ≈˘⟨ ∙-cong ≈refl (invˡ-law x) ⟩
    x ∙ y ∙ (x ⁻¹ ∙ x)                 ≈˘⟨ assoc-law (x ∙ y) (x ⁻¹) x ⟩
    x ∙ y ∙ x ⁻¹ ∙ x                   ≈˘⟨ ∙-cong (idʳ-law (x ∙ y ∙ x ⁻¹)) ≈refl ⟩
    x ∙ y ∙ x ⁻¹ ∙ ε ∙ x               ≈˘⟨ ∙-cong (∙-cong ≈refl (invˡ-law y)) ≈refl ⟩
    x ∙ y ∙ x ⁻¹ ∙ (y ⁻¹ ∙ y) ∙ x      ≈˘⟨ ∙-cong (assoc-law (x ∙ y ∙ x ⁻¹) (y ⁻¹) y) ≈refl ⟩
    x ∙ y ∙ x ⁻¹ ∙ y ⁻¹ ∙ y ∙ x        ≈⟨ assoc-law (comm x y) y x ⟩
    comm x y ∙ (y ∙ x)                 ≈⟨ ∙-cong h ≈refl ⟩
    ε ∙ (y ∙ x)                        ≈⟨ idˡ-law (y ∙ x) ⟩
    y ∙ x                              ∎
```

The contrapositive is the form the support-shrinking iteration consumes: a non-commuting pair of coordinate values keeps the commutator of the tuples away from the identity at that coordinate.

```agda
  -- Non-commuting elements have a nontrivial commutator.
  ¬commutes→comm≉ε : ∀ x y → ¬ Commutes x y → ¬ comm x y ≈ ε
  ¬commutes→comm≉ε x y nc h = nc (comm≈ε→commutes x y h)
```

The forward direction closes the equivalence; it is the same telescope read backwards, recorded so that consumers never redo the rearrangement.

```agda
  -- Commuting elements have a trivial commutator.
  commutes→comm≈ε : ∀ x y → Commutes x y → comm x y ≈ ε
  commutes→comm≈ε x y c = begin
    x ∙ y ∙ x ⁻¹ ∙ y ⁻¹        ≈⟨ ∙-cong (∙-cong c ≈refl) ≈refl ⟩
    y ∙ x ∙ x ⁻¹ ∙ y ⁻¹        ≈⟨ ∙-cong (assoc-law y x (x ⁻¹)) ≈refl ⟩
    y ∙ (x ∙ x ⁻¹) ∙ y ⁻¹      ≈⟨ ∙-cong (∙-cong ≈refl (invʳ-law x)) ≈refl ⟩
    y ∙ ε ∙ y ⁻¹               ≈⟨ ∙-cong (idʳ-law y) ≈refl ⟩
    y ∙ y ⁻¹                   ≈⟨ invʳ-law y ⟩
    ε                          ∎
```
