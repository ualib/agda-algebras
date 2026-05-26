---
layout: default
file: "src/Examples/Classical/CommutativeMonoid.lagda.md"
title: "Examples.Classical.CommutativeMonoid module"
date: "2026-05-24"
author: "the agda-algebras development team"
---

### <a id="examples-classical-commutativemonoid">Worked example — `(ℕ, +, 0)` as a commutative monoid</a>

This is the [Examples.Classical.CommutativeMonoid][] module of the [Agda Universal Algebra Library][].

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Classical.CommutativeMonoid where

-- Imports from the Agda Standard Library -------------------------------------
open import Data.Nat                               using  ( ℕ ; _+_ ; zero )
open import Data.Nat.Properties                    using  ( +-assoc ; +-identityˡ
                                                          ; +-identityʳ ; +-comm )
open import Relation.Binary.PropositionalEquality  using  ( _≡_ ; refl )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Small.Structures.CommutativeMonoid
  using  ( CommutativeMonoid ; eqsToCommutativeMonoid )

import Classical.Structures.CommutativeMonoid as Polymorphic
```

We construct `(ℕ, +, 0)` from stdlib's `+-assoc`, `+-identityˡ`, `+-identityʳ`,
`+-comm`.

```agda
ℕ-commutativeMonoid : CommutativeMonoid
ℕ-commutativeMonoid = eqsToCommutativeMonoid ℕ _+_ zero +-assoc +-identityˡ +-identityʳ +-comm

open Polymorphic.CommutativeMonoid-Op ℕ-commutativeMonoid using ( _∙_ ; ε )

∙-is-+-cmn : ∀ (a b : ℕ) → a ∙ b ≡ a + b
∙-is-+-cmn a b = refl

ε-is-0-cmn : ε ≡ zero
ε-is-0-cmn = refl
```

--------------------------------------

{% include UALib.Links.md %}
