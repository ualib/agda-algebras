---
layout: default
file: "src/Examples/Classical/CommutativeRing.lagda.md"
title: "Examples.Classical.CommutativeRing module"
date: "2026-05-30"
author: "the agda-algebras development team"
---

### Worked example: `(ℤ, +, *, 0, 1, -)` as a commutative ring {#examples-classical-commutativering}

This is the [Examples.Classical.CommutativeRing][] module of the [Agda Universal Algebra Library][].

The integers are the canonical commutative ring; built directly from stdlib's
additive abelian-group laws, multiplicative monoid laws, commutativity, and the two
distributivity laws.  This module discharges the M3-8 acceptance criteria: the
worked example `ℤ-commutativeRing` type-checks, and the bridge to stdlib's
`CommutativeRing` round-trips on `ℤ`.

The ring's curried accessors are opened under fresh names (`_⊕_`, `_⊗_`, `⊝_`,
`e₀`, `e₁`) so they do not clash with `Data.Integer`'s own `_+_`, `_*_`, `-_`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Classical.CommutativeRing where

-- Imports from the Agda Standard Library -------------------------------------
open import Data.Integer             using ( ℤ ; _+_ ; _*_ ; 0ℤ ; 1ℤ ; -_ )
open import Data.Integer.Properties  using ( +-assoc ; +-identityˡ ; +-identityʳ
                                           ; +-inverseˡ ; +-inverseʳ ; +-comm
                                           ; *-assoc ; *-identityˡ ; *-identityʳ ; *-comm
                                           ; *-distribˡ-+ ; *-distribʳ-+ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Bundles.CommutativeRing using ( ⟨_⟩ᶜʳᵍ ; ⟪_⟫ᶜʳᵍ )
open import Classical.Small.Structures.CommutativeRing
  using ( CommutativeRing ; eqsToCommutativeRing )

import Classical.Structures.CommutativeRing as Polymorphic
```

#### The commutative ring `(ℤ, +, *, 0, 1, -)` {#integer-commutativering}

```agda
ℤ-commutativeRing : CommutativeRing
ℤ-commutativeRing =
  eqsToCommutativeRing ℤ _+_ 0ℤ -_ _*_ 1ℤ
    +-assoc +-identityˡ +-identityʳ +-inverseˡ +-inverseʳ +-comm
    *-assoc *-identityˡ *-identityʳ *-comm
    *-distribˡ-+ *-distribʳ-+

open Polymorphic.CommutativeRing-Op ℤ-commutativeRing using ()
  renaming ( _+_ to _⊕_ ; _·_ to _⊗_ ; 0R to e₀ ; 1R to e₁ ; -_ to ⊝_ )
```

#### Acceptance checks

The curried accessors compute to the underlying integer operations.

```agda
⊕-is-+-cr : ∀ (a b : ℤ) → a ⊕ b ≡ a + b
⊕-is-+-cr a b = refl

⊗-is-*-cr : ∀ (a b : ℤ) → a ⊗ b ≡ a * b
⊗-is-*-cr a b = refl

e₀-is-0ℤ-cr : e₀ ≡ 0ℤ
e₀-is-0ℤ-cr = refl

e₁-is-1ℤ-cr : e₁ ≡ 1ℤ
e₁-is-1ℤ-cr = refl

⊝-is-neg-cr : ∀ (a : ℤ) → ⊝ a ≡ - a
⊝-is-neg-cr a = refl
```

The bridge to stdlib's `CommutativeRing` round-trips pointwise on every operation.

```agda
open Polymorphic.CommutativeRing-Op ⟪ ⟨ ℤ-commutativeRing ⟩ᶜʳᵍ ⟫ᶜʳᵍ using ()
  renaming ( _+_ to _⊕'_ ; _·_ to _⊗'_ ; 0R to e₀' ; 1R to e₁' ; -_ to ⊝'_ )

roundtrip-⊕-cr : ∀ (a b : ℤ) → a ⊕' b ≡ a + b
roundtrip-⊕-cr a b = refl

roundtrip-⊗-cr : ∀ (a b : ℤ) → a ⊗' b ≡ a * b
roundtrip-⊗-cr a b = refl

roundtrip-e₀-cr : e₀' ≡ 0ℤ
roundtrip-e₀-cr = refl

roundtrip-e₁-cr : e₁' ≡ 1ℤ
roundtrip-e₁-cr = refl

roundtrip-⊝-cr : ∀ (a : ℤ) → ⊝' a ≡ - a
roundtrip-⊝-cr a = refl
```

--------------------------------------

<span style="float:left;">[← Examples.Classical.AbelianGroup](Examples.Classical.AbelianGroup.html)</span>

{% include UALib.Links.md %}
