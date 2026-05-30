---
layout: default
file: "src/Examples/Classical/Group.lagda.md"
title: "Examples.Classical.Group module"
date: "2026-05-30"
author: "the agda-algebras development team"
---

### <a id="examples-classical-group">Worked example — `(ℤ, +, 0, -)` as a group</a>

This is the [Examples.Classical.Group][] module of the [Agda Universal Algebra Library][].

The integers under addition form the canonical group; built directly from stdlib's
`+-assoc`, `+-identityˡ`, `+-identityʳ`, `+-inverseˡ`, `+-inverseʳ`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Classical.Group where

-- Imports from the Agda Standard Library -------------------------------------
open import Data.Integer             using ( ℤ ; _+_ ; 0ℤ ; -_ )
open import Data.Integer.Properties  using ( +-assoc ; +-identityˡ ; +-identityʳ
                                           ; +-inverseˡ ; +-inverseʳ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Bundles.Group           using ( ⟨_⟩ᵍʳ ; ⟪_⟫ᵍʳ )
open import Classical.Small.Structures.Group  using ( Group ; eqsToGroup )

import Classical.Structures.Group as Polymorphic
```

#### <a id="integer-group">The group `(ℤ, +, 0, -)`</a>

```agda
ℤ-group : Group
ℤ-group = eqsToGroup ℤ _+_ 0ℤ -_ +-assoc +-identityˡ +-identityʳ +-inverseˡ +-inverseʳ

open Polymorphic.Group-Op ℤ-group using ( _∙_ ; ε ; _⁻¹ )
```

#### <a id="acceptance">Acceptance checks</a>

```agda
∙-is-+-gr : ∀ (a b : ℤ) → a ∙ b ≡ a + b
∙-is-+-gr a b = refl

ε-is-0-gr : ε ≡ 0ℤ
ε-is-0-gr = refl

⁻¹-is-neg-gr : ∀ (a : ℤ) → a ⁻¹ ≡ - a
⁻¹-is-neg-gr a = refl
```

The bundle round-trips pointwise on the operation, the identity, and the inverse.

```agda
open Polymorphic.Group-Op ⟪ ⟨ ℤ-group ⟩ᵍʳ ⟫ᵍʳ using () renaming ( _∙_ to _·_ ; ε to ε· ; _⁻¹ to _⁻¹· )

roundtrip-∙-gr : ∀ (a b : ℤ) → a · b ≡ a + b
roundtrip-∙-gr a b = refl

roundtrip-ε-gr : ε· ≡ 0ℤ
roundtrip-ε-gr = refl

roundtrip-⁻¹-gr : ∀ (a : ℤ) → a ⁻¹· ≡ - a
roundtrip-⁻¹-gr a = refl
```

--------------------------------------

<span style="float:left;">[← Examples.Classical.Monoid](Examples.Classical.Monoid.html)</span>
<span style="float:right;">[Examples.Classical.AbelianGroup →](Examples.Classical.AbelianGroup.html)</span>

{% include UALib.Links.md %}
