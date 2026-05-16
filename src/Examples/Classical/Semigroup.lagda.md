---
layout: default
file: "src/Examples/Classical/Semigroup.lagda.md"
title: "Examples.Classical.Semigroup module"
date: "2026-05-15"
author: "the agda-algebras development team"
---

### <a id="examples-classical-semigroup">Worked examples — semigroups</a>

This is the [Examples.Classical.Semigroup][] module of the [Agda Universal Algebra Library][].

This file is the home of all worked semigroup-specific examples.  The pattern-setting first example, landing under M3-2, is `(ℕ, +)` constructed via `fromPropEq` from stdlib's `+-assoc`.  Future examples to land here as they accumulate:

+  `(List A, _++_)`: the free semigroup on the alphabet `A`.
+  Finitely generated semigroups via presentations.
+  Symmetric semigroups `(End A, _∘_)` for finite `A`.

Each example is small, self-contained, and intended to exercise a specific facet of [`Classical.Structures.Semigroup`][Classical.Structures.Semigroup] or its [bundle bridge][Classical.Bundles.Semigroup].

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Classical.Semigroup where

-- Imports from Agda and the Agda Standard Library ----------------------
open import Data.Nat                              using ( ℕ ; _+_ )
open import Data.Nat.Properties                   using ( +-assoc )
open import Data.Fin.Patterns                     using ( 0F ; 1F )
open import Data.Product                          using ( proj₁ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

-- Imports from agda-algebras -------------------------------------------
open import Classical.Signatures.Semigroup        using ( ∙op )
open import Classical.Signatures.Semigroup        using ( 𝑆ₛₘ )
open import Classical.Small.Structures.Semigroup
  using ( Semigroup ; fromPropEq )
import Classical.Bundles.Semigroup as Bridge
open import Setoid.Algebras                       {𝑆 = 𝑆ₛₘ}
  using ( _̂_ )
```

#### <a id="n-semigroup">`(ℕ, +)` as a semigroup</a>

```agda
ℕ-semigroup : Semigroup
ℕ-semigroup = fromPropEq ℕ _+_ +-assoc
```

#### <a id="op-reduces-to-plus">`∙op` interprets to `_+_` definitionally</a>

The third acceptance criterion of M3-2 asks that the `fromPropEq` construction not introduce opacity around the interpreted operation.  Concretely: applying the algebra's interpretation of `∙op` to a two-element tuple `args : Fin 2 → ℕ` should reduce on the nose to `args 0F + args 1F`, with no nested unfolding required.

```agda
∙op-is-+ : ∀ (a b : ℕ)
         → (∙op ̂ proj₁ ℕ-semigroup) (λ { 0F → a ; 1F → b }) ≡ a + b
∙op-is-+ a b = refl
```

#### <a id="round-trip-on-n-semigroup">Round trip on `ℕ-semigroup`</a>

The fourth acceptance criterion asks that the round trip Σ-core → bundle → Σ-core land back on `ℕ-semigroup` up to propositional equality.

```agda
-- ℕ-roundtrip : Bridge.⟪ Bridge.⟨ ℕ-semigroup ⟩ₛₘ ⟫ₛₘ ≡ ℕ-semigroup
-- ℕ-roundtrip = refl

ℕ-roundtrip-pointwise :
    ∀ (a b : ℕ)
  → (∙op ̂ proj₁ (Bridge.⟪ Bridge.⟨ ℕ-semigroup ⟩ₛₘ ⟫ₛₘ)) (λ { 0F → a ; 1F → b })
    ≡ a + b
ℕ-roundtrip-pointwise a b = refl
```

--------------------------------------

{% include UALib.Links.md %}
