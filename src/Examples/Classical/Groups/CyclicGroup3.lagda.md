---
layout: default
file: "src/Examples/Classical/Groups/CyclicGroup3.lagda.md"
title: "Examples.Classical.Groups.CyclicGroup3 module"
date: "2026-05-31"
author: "the agda-algebras development team"
---

### Worked example: the cyclic group `ℤ/3ℤ` from a Cayley table

This is the [Examples.Classical.Groups.CyclicGroup3][] module of the [Agda Universal Algebra Library][].

The integers modulo `3` under addition form the smallest non-trivial cyclic group.
We build it on the carrier `Fin 3` from its addition table, using the Cayley-table
machinery of [`Overture.Cayley`][Overture.Cayley]: the group axioms are decidable over the finite
carrier, so associativity, the identity laws, and the inverse laws are each
discharged by `from-yes`{.AgdaFunction} applied to the corresponding decision.  This
is the first example to exercise the `Associative?`{.AgdaFunction},
`LeftIdentity?`{.AgdaFunction}, `RightIdentity?`{.AgdaFunction},
`LeftInverse?`{.AgdaFunction}, and `RightInverse?`{.AgdaFunction} checkers, and the
first to feed a tabulated operation to `eqsToGroup`{.AgdaFunction}.

The addition table (rows indexed by the left summand, columns by the right; entry
`a , b` is `(a + b) mod 3`):

| + | 0 | 1 | 2 |
|---|---|---|---|
| 0 | 0 | 1 | 2 |
| 1 | 1 | 2 | 0 |
| 2 | 2 | 0 | 1 |

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Classical.Groups.CyclicGroup3 where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Data.Fin                                using ( Fin )
open import Data.Fin.Patterns                       using ( 0F ; 1F ; 2F )
open import Data.Vec.Base                           using ( _∷_ ; [] )
open import Relation.Binary.PropositionalEquality   using ( _≡_ ; refl )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Cayley                   using  ( Table ; ⟦_⟧ ; from-yes )
open import Overture.Operations.Properties    using  ( Associative? ; Commutative?
                                                     ; LeftIdentity? ; RightIdentity?
                                                     ; LeftInverse? ; RightInverse? )
open import Classical.Bundles.Group           using  ( ⟨_⟩ᵍᵖ ; ⟪_⟫ᵍᵖ )
open import Classical.Small.Structures.Group  using  ( Group ; eqsToGroup )

import Classical.Structures.Group as Polymorphic
```
-->

#### The Cayley table, the operation, and the inverse map

```agda
-- The addition-mod-3 table.
z3-table : Table 3
z3-table = (0F ∷ 1F ∷ 2F ∷ [])
         ∷ (1F ∷ 2F ∷ 0F ∷ [])
         ∷ (2F ∷ 0F ∷ 1F ∷ [])
         ∷ []

-- The operation it denotes.
_·_ : Fin 3 → Fin 3 → Fin 3
_·_ = ⟦ z3-table ⟧

-- The inverse map: 0 ↦ 0, 1 ↦ 2, 2 ↦ 1 (negation mod 3).
z3-inv : Fin 3 → Fin 3
z3-inv 0F = 0F
z3-inv 1F = 2F
z3-inv 2F = 1F
```

#### The group `ℤ/3ℤ`

The five group axioms are decidable; `from-yes`{.AgdaFunction} extracts each proof.
If the table were not associative, or `0F`{.AgdaInductiveConstructor} were not an
identity, or `z3-inv`{.AgdaFunction} were not an inverse, the corresponding decision
would reduce to `no`{.AgdaInductiveConstructor} and this definition would fail to
type-check.

```agda
z3-group : Group
z3-group = eqsToGroup (Fin 3) _·_ 0F z3-inv
  (from-yes (Associative?   _·_)) (from-yes (LeftIdentity?  _·_ 0F))
  (from-yes (RightIdentity? _·_ 0F)) (from-yes (LeftInverse?   _·_ 0F z3-inv))
  (from-yes (RightInverse?  _·_ 0F z3-inv))

open Polymorphic.Group-Op z3-group using ( _∙_ ; ε ; _⁻¹ )
```

#### `ℤ/3ℤ` is abelian

```agda
·-comm : ∀ a b → a · b ≡ b · a
·-comm = from-yes (Commutative? _·_)
```

#### Acceptance checks

The `Group-Op`{.AgdaModule} accessors interpret to the tabulated operation, to
`0F`{.AgdaInductiveConstructor}, and to `z3-inv`{.AgdaFunction} on the nose; discharged
by `refl`{.AgdaInductiveConstructor}.

```agda
∙-is-· : ∀ (a b : Fin 3) → a ∙ b ≡ a · b
∙-is-· a b = refl

ε-is-0 : ε ≡ 0F
ε-is-0 = refl

⁻¹-is-inv : ∀ (a : Fin 3) → a ⁻¹ ≡ z3-inv a
⁻¹-is-inv a = refl
```

The bundle bridge round-trips on `z3-group`{.AgdaFunction} pointwise on the operation,
the identity, and the inverse.

```agda
open Polymorphic.Group-Op ⟪ ⟨ z3-group ⟩ᵍᵖ ⟫ᵍᵖ using ()
  renaming ( _∙_ to _·′_ ; ε to ε′ ; _⁻¹ to _⁻¹′ )

roundtrip-∙ : ∀ (a b : Fin 3) → a ·′ b ≡ a · b
roundtrip-∙ a b = refl

roundtrip-ε : ε′ ≡ 0F
roundtrip-ε = refl

roundtrip-⁻¹ : ∀ (a : Fin 3) → a ⁻¹′ ≡ z3-inv a
roundtrip-⁻¹ a = refl
```
