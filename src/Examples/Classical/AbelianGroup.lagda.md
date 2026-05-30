---
layout: default
file: "src/Examples/Classical/AbelianGroup.lagda.md"
title: "Examples.Classical.AbelianGroup module"
date: "2026-05-30"
author: "the agda-algebras development team"
---

### <a id="examples-classical-abeliangroup">Worked example — `(ℤ, +, 0, -)` as an abelian group</a>

This is the [Examples.Classical.AbelianGroup][] module of the [Agda Universal Algebra Library][].

The integers under addition are the canonical abelian group — the same carrier and
operations as the [`Group`][Examples.Classical.Group] example, now additionally
witnessing commutativity via stdlib's `+-comm`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Classical.AbelianGroup where

-- Imports from the Agda Standard Library -------------------------------------
open import Data.Integer             using ( ℤ ; _+_ ; 0ℤ ; -_ )
open import Data.Integer.Properties  using ( +-assoc ; +-identityˡ ; +-identityʳ
                                           ; +-inverseˡ ; +-inverseʳ ; +-comm )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Bundles.AbelianGroup           using ( ⟨_⟩ᵃᵍ ; ⟪_⟫ᵃᵍ )
open import Classical.Small.Structures.AbelianGroup  using ( AbelianGroup ; eqsToAbelianGroup )

import Classical.Structures.AbelianGroup as Polymorphic
```

#### <a id="integer-abeliangroup">The abelian group `(ℤ, +, 0, -)`</a>

```agda
ℤ-abelianGroup : AbelianGroup
ℤ-abelianGroup =
  eqsToAbelianGroup ℤ _+_ 0ℤ -_ +-assoc +-identityˡ +-identityʳ +-inverseˡ +-inverseʳ +-comm

open Polymorphic.AbelianGroup-Op ℤ-abelianGroup using ( _∙_ ; ε ; _⁻¹ )
```

#### <a id="acceptance">Acceptance checks</a>

```agda
∙-is-+-ag : ∀ (a b : ℤ) → a ∙ b ≡ a + b
∙-is-+-ag a b = refl

ε-is-0-ag : ε ≡ 0ℤ
ε-is-0-ag = refl

⁻¹-is-neg-ag : ∀ (a : ℤ) → a ⁻¹ ≡ - a
⁻¹-is-neg-ag a = refl
```

The bundle round-trips pointwise on the operation, the identity, and the inverse.

```agda
open Polymorphic.AbelianGroup-Op ⟪ ⟨ ℤ-abelianGroup ⟩ᵃᵍ ⟫ᵃᵍ using ()
  renaming ( _∙_ to _·_ ; ε to ε· ; _⁻¹ to _⁻¹· )

roundtrip-∙-ag : ∀ (a b : ℤ) → a · b ≡ a + b
roundtrip-∙-ag a b = refl

roundtrip-ε-ag : ε· ≡ 0ℤ
roundtrip-ε-ag = refl

roundtrip-⁻¹-ag : ∀ (a : ℤ) → a ⁻¹· ≡ - a
roundtrip-⁻¹-ag a = refl
```

--------------------------------------

<span style="float:left;">[← Examples.Classical.Group](Examples.Classical.Group.html)</span>

{% include UALib.Links.md %}
