---
layout: default
file: "src/Examples/Classical/CommutativeIdempotentMagma.lagda.md"
title: "Examples.Classical.CommutativeIdempotentMagma module"
date: "2026-05-31"
author: "the agda-algebras development team"
---

### Worked example — a commutative idempotent magma from a Cayley table

This is the [Examples.Classical.CommutativeIdempotentMagma][] module of the [Agda Universal Algebra Library][].

This is the first finite worked example built from a *Cayley table* (see
[`Overture.Cayley`][]).  We fix a four-element carrier `Fin 4` and a binary operation
given outright by its multiplication table, then read off its algebraic shape: the
operation is *commutative* and *idempotent*, so `(Fin 4, _·_)` is a magma with a
commutative idempotent operation.  It is deliberately *not* associative, which makes
it a genuine magma — it is not a semilattice, and not even a semigroup.

The table is the following, with rows indexed by the left argument and columns by
the right argument (`0`–`3` abbreviate `0F`–`3F`):

| · | 0 | 1 | 2 | 3 |
|---|---|---|---|---|
| 0 | 0 | 2 | 0 | 3 |
| 1 | 2 | 1 | 3 | 1 |
| 2 | 0 | 3 | 2 | 2 |
| 3 | 3 | 1 | 2 | 3 |

The table is symmetric (hence the operation is commutative) and its diagonal is
the identity (hence the operation is idempotent).

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Classical.CommutativeIdempotentMagma where

-- Imports from the Agda Standard Library -------------------------------------
open import Data.Fin                                using ( Fin )
open import Data.Fin.Patterns                       using ( 0F ; 1F ; 2F ; 3F )
open import Data.Product                            using ( ∃-syntax ; _,_ )
open import Data.Vec.Base                           using ( _∷_ ; [] )
open import Relation.Binary.PropositionalEquality   using ( _≡_ ; _≢_ ; refl )
open import Relation.Nullary.Negation.Core          using ( ¬_ ; contradiction )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Cayley                         using  ( Table ; ⟦_⟧ ; from-yes )
open import Overture.Operations.Properties          using  ( Commutative? ; Idempotent? )
open import Classical.Bundles.Magma                 using  ( ⟨_⟩ᵐᵃ ; ⟪_⟫ᵐᵃ )
open import Classical.Small.Structures.Magma        using  ( Magma ; opsToMagma )

import Classical.Structures.Magma as Polymorphic
```

#### The Cayley table and its operation

```agda
-- The Cayley table, written out row by row.
cim-table : Table 4
cim-table = (0F ∷ 2F ∷ 0F ∷ 3F ∷ [])
          ∷ (2F ∷ 1F ∷ 3F ∷ 1F ∷ [])
          ∷ (0F ∷ 3F ∷ 2F ∷ 2F ∷ [])
          ∷ (3F ∷ 1F ∷ 2F ∷ 3F ∷ [])
          ∷ []

-- The operation it denotes.
_·_ : Fin 4 → Fin 4 → Fin 4
_·_ = ⟦ cim-table ⟧
```

#### The magma `(Fin 4, _·_)`

```agda
cim-magma : Magma
cim-magma = opsToMagma (Fin 4) _·_

open Polymorphic.Magma-Op cim-magma using ( _∙_ )
```

#### Commutativity and idempotence

Both laws are decidable over the finite carrier, so each is discharged by
`from-yes`{.AgdaFunction} applied to the corresponding decision from
[`Overture.Cayley`][].  No case dump is written by hand; if the table
violated a law the decision would reduce to `no`{.AgdaInductiveConstructor} and
the term would fail to type-check.

```agda
·-comm : ∀ a b → a · b ≡ b · a
·-comm = from-yes (Commutative? _·_)

·-idem : ∀ a → a · a ≡ a
·-idem = from-yes (Idempotent? _·_)
```

#### The operation is not associative

A single triple witnesses the failure of associativity: `(0 · 1) · 2` reduces to
`2` while `0 · (1 · 2)` reduces to `3`.  Stated existentially, *some* triple
distinguishes the two bracketings; the witnessing inequality is the absurd pattern
`λ ()`{.AgdaFunction}, since the goal `2 ≡ 3` is uninhabited.

```agda
·-not-associative : ∃[ a ] ∃[ b ] ∃[ c ] (a · b) · c ≢ a · (b · c)
·-not-associative = 0F , 1F , 2F , λ ()
```

The same fact in negated-universal form — the operation admits no proof of
associativity, so the magma is not a semigroup — follows by feeding the witnessing
triple to the assumed associativity and deriving a contradiction.

```agda
·-not-a-semigroup : ¬ (∀ a b c → (a · b) · c ≡ a · (b · c))
·-not-a-semigroup assoc = contradiction (assoc 0F 1F 2F) λ ()
```

#### Acceptance checks

The `Magma-Op`{.AgdaModule} accessor interprets to the tabulated operation on the
nose, with no opacity from `opsToMagma`{.AgdaFunction} or the `Curry₂`{.AgdaFunction}
wrapping; discharged by `refl`{.AgdaInductiveConstructor}.

```agda
∙-is-·-ma : ∀ (a b : Fin 4) → a ∙ b ≡ a · b
∙-is-·-ma a b = refl
```

The bundle bridge round-trips on `cim-magma`{.AgdaFunction} pointwise, as for the
other magma examples (per [ADR-002 v2](../../docs/adr/002-classical-layer-design.md) §6).

```agda
open Polymorphic.Magma-Op ⟪ ⟨ cim-magma ⟩ᵐᵃ ⟫ᵐᵃ using () renaming ( _∙_ to _·′_ )

roundtrip-cim-ma : ∀ (a b : Fin 4) → a ·′ b ≡ a · b
roundtrip-cim-ma a b = refl
```
