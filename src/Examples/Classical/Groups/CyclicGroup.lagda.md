---
layout: default
file: "src/Examples/Classical/Groups/CyclicGroup.lagda.md"
title: "Examples.Classical.Groups.CyclicGroup module"
date: "2026-05-30"
author: "the agda-algebras development team"
---

### Worked example: `(ℤ, +, 0, -)` as a group

This is the [Examples.Classical.Groups.CyclicGroup][] module of the [Agda Universal Algebra Library][].

The integers under addition form the canonical group — indeed the infinite cyclic
group; built directly from stdlib's
`+-assoc`, `+-identityˡ`, `+-identityʳ`, `+-inverseˡ`, `+-inverseʳ`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Classical.Groups.CyclicGroup where

-- Imports from the Agda Standard Library -------------------------------------
open import Data.Integer             using ( ℤ ; _+_ ; 0ℤ ; -_ )
open import Data.Integer.Properties  using ( +-assoc ; +-identityˡ ; +-identityʳ
                                           ; +-inverseˡ ; +-inverseʳ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Bundles.Group           using ( ⟨_⟩ᵍᵖ ; ⟪_⟫ᵍᵖ )
open import Classical.Small.Structures.Group  using ( Group ; eqsToGroup )

import Classical.Structures.Group as Polymorphic
```

#### The group `(ℤ, +, 0, -)` {#integer-group}

```agda
ℤ-group : Group
ℤ-group = eqsToGroup ℤ _+_ 0ℤ -_ +-assoc +-identityˡ +-identityʳ +-inverseˡ +-inverseʳ

open Polymorphic.Group-Op ℤ-group using ( _∙_ ; ε ; _⁻¹ )
```

#### Acceptance checks

```agda
∙-is-+-group : ∀ (a b : ℤ) → a ∙ b ≡ a + b
∙-is-+-group a b = refl

ε-is-0-group : ε ≡ 0ℤ
ε-is-0-group = refl

⁻¹-is-neg-group : ∀ (a : ℤ) → a ⁻¹ ≡ - a
⁻¹-is-neg-group a = refl
```

The bundle round-trips pointwise on the operation, the identity, and the inverse.

```agda
open Polymorphic.Group-Op ⟪ ⟨ ℤ-group ⟩ᵍᵖ ⟫ᵍᵖ using () renaming ( _∙_ to _·_ ; ε to ε· ; _⁻¹ to _⁻¹· )

roundtrip-∙-group : ∀ (a b : ℤ) → a · b ≡ a + b
roundtrip-∙-group a b = refl

roundtrip-ε-group : ε· ≡ 0ℤ
roundtrip-ε-group = refl

roundtrip-⁻¹-group : ∀ (a : ℤ) → a ⁻¹· ≡ - a
roundtrip-⁻¹-group a = refl
```

--------------------------------------

<span style="float:left;">[← Examples.Classical.Monoid](Examples.Classical.Monoid.html)</span>
<span style="float:right;">[Examples.Classical.Groups.AbelianGroup →](Examples.Classical.Groups.AbelianGroup.html)</span>

{% include UALib.Links.md %}
