---
layout: default
title : "Overture.Operations.Properties module (The Agda Universal Algebra Library)"
date : "2026-05-31"
author: "the agda-algebras development team"
---

### Decidable equational properties of finite operations

This is the [Overture.Operations.Properties][] module of the [Agda Universal Algebra Library][].

Decision procedures for the standard equational laws of a binary operation over a
*finite* carrier.  Each law `∀ a … → … ≡ …` is decidable because the carrier `Fin n`
is finitely searchable (`Data.Fin.Properties.all?`) and has decidable equality
(`_≟_`); the checkers below expose that decision so that a caller can extract the
proof with `from-yes` (re-exported from [`Overture.Cayley`][Overture.Cayley]) whenever the operation
satisfies the law.

These are the *evaluated* analogues of the syntactic equation builders in
[`Classical.Equations`][Classical.Equations], and the finite, decidable counterparts of the law
predicates in the standard library's `Algebra.Definitions`.  They are stated for an
arbitrary finite operation `Fin n → Fin n → Fin n`: a Cayley table (via
[`Overture.Cayley`][Overture.Cayley]) is one way to present such an operation, but the checkers do
not depend on that representation, which is why they live here rather than in the
`Cayley` module.

The single-operation checkers — associativity, commutativity, idempotency, and the
identity/inverse laws — serve the finite-group and -magma examples; the two-operation
checkers — absorption and distributivity — serve the finite-lattice examples.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Overture.Operations.Properties where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Data.Nat                                using ( ℕ )
open import Data.Fin                                using ( Fin )
open import Data.Fin.Properties                     using ( _≟_ ; all? )
open import Relation.Binary.PropositionalEquality   using ( _≡_ )
open import Relation.Nullary.Decidable.Core         using ( Dec )
```
-->

#### Laws of a single operation

These are stated for an arbitrary binary operation `_·_` over the finite carrier.

```agda
module _ {n : ℕ} (_·_ : Fin n → Fin n → Fin n) where

  -- a · a ≡ a for every a.
  Idempotent? : Dec (∀ a → a · a ≡ a)
  Idempotent? = all? (λ a → (a · a) ≟ a)

  -- a · b ≡ b · a for every a, b.
  Commutative? : Dec (∀ a b → a · b ≡ b · a)
  Commutative? = all? (λ a → all? (λ b → (a · b) ≟ (b · a)))

  -- (a · b) · c ≡ a · (b · c) for every a, b, c.
  Associative? : Dec (∀ a b c → (a · b) · c ≡ a · (b · c))
  Associative? = all? (λ a → all? (λ b → all? (λ c → ((a · b) · c) ≟ (a · (b · c)))))

  module _ (e : Fin n) where

    -- e · a ≡ a for every a.
    LeftIdentity? : Dec (∀ a → e · a ≡ a)
    LeftIdentity? = all? (λ a → (e · a) ≟ a)

    -- a · e ≡ a for every a.
    RightIdentity? : Dec (∀ a → a · e ≡ a)
    RightIdentity? = all? (λ a → (a · e) ≟ a)

    module _ (i : Fin n → Fin n) where

      -- (i a) · a ≡ e for every a.
      LeftInverse? : Dec (∀ a → (i a) · a ≡ e)
      LeftInverse? = all? (λ a → ((i a) · a) ≟ e)

      -- a · (i a) ≡ e for every a.
      RightInverse? : Dec (∀ a → a · (i a) ≡ e)
      RightInverse? = all? (λ a → (a · (i a)) ≟ e)
```

#### Laws relating two operations

These take two operations `_·_` and `_∘_`; in a lattice they are typically `∧` and
`∨`.  The shapes match the evaluated forms of `Classical.Equations`'s `AbsorbsLeft`,
`AbsorbsRight`, `DistributesOverˡ`, and `DistributesOverʳ`.

```agda
module _ {n : ℕ} (_·_ _∘_ : Fin n → Fin n → Fin n) where

  -- a · (a ∘ b) ≡ a
  Absorbsˡ? : Dec (∀ a b → a · (a ∘ b) ≡ a)
  Absorbsˡ? = all? (λ a → all? (λ b → (a · (a ∘ b)) ≟ a))

  -- (a · b) ∘ a ≡ a
  Absorbsʳ? : Dec (∀ a b → (a · b) ∘ a ≡ a)
  Absorbsʳ? = all? (λ a → all? (λ b → ((a · b) ∘ a) ≟ a))

  -- a · (b ∘ c) ≡ (a · b) ∘ (a · c)
  Distributesˡ? : Dec (∀ a b c → a · (b ∘ c) ≡ (a · b) ∘ (a · c))
  Distributesˡ? = all? (λ a → all? (λ b → all? (λ c → (a · (b ∘ c)) ≟ ((a · b) ∘ (a · c)))))

  -- (b ∘ c) · a ≡ (b · a) ∘ (c · a)
  Distributesʳ? : Dec (∀ a b c → (b ∘ c) · a ≡ (b · a) ∘ (c · a))
  Distributesʳ? = all? (λ a → all? (λ b → all? (λ c → ((b ∘ c) · a) ≟ ((b · a) ∘ (c · a)))))
```
