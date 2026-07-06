---
layout: default
file: "src/Examples/Classical/Monoid.lagda.md"
title: "Examples.Classical.Monoid module"
date: "2026-05-24"
author: "the agda-algebras development team"
---

### Worked example: `(List ℕ, ++, [])` as a monoid {#examples-classical-monoid}

This is the [Examples.Classical.Monoid][] module of the [Agda Universal Algebra Library][].

Lists under concatenation form the canonical monoid, and a deliberately
*non-commutative* one — so the corpus carries a witness that a monoid need not be
commutative, in contrast to the `(ℕ, +, 0)` commutative monoid of
[`Examples.Classical.CommutativeMonoid`][].  Built directly from stdlib's `++-assoc`,
`++-identityˡ`, `++-identityʳ`.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Classical.Monoid where

-- Imports from the Agda Standard Library -------------------------------------
open import Data.List             using ( List ; [] ; _++_ )
open import Data.List.Properties  using ( ++-assoc ; ++-identityˡ ; ++-identityʳ )
open import Data.Nat              using ( ℕ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Bundles.Monoid           using ( ⟨_⟩ᵐᵒ ; ⟪_⟫ᵐᵒ )
open import Classical.Small.Structures.Monoid  using ( Monoid ; eqsToMonoid )

import Classical.Structures.Monoid as Polymorphic
```
-->

#### The monoid `(List ℕ, ++, [])` {#list-monoid}

```agda
list-monoid : Monoid
list-monoid = eqsToMonoid (List ℕ) _++_ [] ++-assoc ++-identityˡ ++-identityʳ

open Polymorphic.Monoid-Op list-monoid using ( _∙_ ; ε )
```

#### Acceptance checks

```agda
∙-is-++-mn : ∀ (xs ys : List ℕ) → xs ∙ ys ≡ xs ++ ys
∙-is-++-mn xs ys = refl

ε-is-[]-mn : ε ≡ []
ε-is-[]-mn = refl
```

The bundle round-trips pointwise on both the operation and the identity.

```agda
open Polymorphic.Monoid-Op ⟪ ⟨ list-monoid ⟩ᵐᵒ ⟫ᵐᵒ
  using () renaming ( _∙_ to _·_ ; ε to ε· )

roundtrip-∙-mn : ∀ (xs ys : List ℕ) → xs · ys ≡ xs ++ ys
roundtrip-∙-mn xs ys = refl

roundtrip-ε-mn : ε· ≡ []
roundtrip-ε-mn = refl
```
