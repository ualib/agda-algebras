---
layout: default
file: "src/Examples/Classical/CommutativeIdempotentMagma.lagda.md"
title: "Examples.Classical.CommutativeIdempotentMagma module"
date: "2026-05-31"
author: "the agda-algebras development team"
---

### <a id="examples-classical-commutative-idempotent-magma">Worked example — a commutative idempotent magma from a Cayley table</a>

This is the [Examples.Classical.CommutativeIdempotentMagma][] module of the [Agda Universal Algebra Library][].

This is the first finite worked example built from a *Cayley table* (see
[`Examples.Classical.Cayley`][]).  We fix a four-element carrier
`Fin 4`{.AgdaDatatype} and a binary operation given outright by its
multiplication table, then read off its algebraic shape: the operation is
*commutative* and *idempotent*, so `(Fin 4, _·_)`{.AgdaFunction} is a magma with
a commutative idempotent operation.  It is deliberately *not* associative, which
makes it a genuine magma — it is not a semilattice, and not even a semigroup.

The table is the following, with rows indexed by the left argument and columns by
the right argument (`0`–`3` abbreviate `0F`–`3F`):

| `·` | 0 | 1 | 2 | 3 |
|-----|---|---|---|---|
| **0** | 0 | 2 | 0 | 3 |
| **1** | 2 | 1 | 3 | 1 |
| **2** | 0 | 3 | 2 | 2 |
| **3** | 3 | 1 | 2 | 3 |

The table is symmetric (hence the operation is commutative) and its diagonal is
the identity `0,1,2,3`{.AgdaInductiveConstructor} (hence the operation is
idempotent).

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Examples.Classical.CommutativeIdempotentMagma where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Data.Fin                                using ( Fin )
open import Data.Fin.Patterns                       using ( 0F ; 1F ; 2F ; 3F )
open import Data.Vec.Base                           using ( _∷_ ; [] )
open import Relation.Binary.PropositionalEquality   using ( _≡_ ; refl )
open import Relation.Nullary.Negation.Core          using ( ¬_ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Examples.Classical.Cayley           using ( Table ; ⟦_⟧ ; from-yes
                                                      ; Commutative? ; Idempotent? )
open import Classical.Bundles.Magma             using ( ⟨_⟩ᵐᵃ ; ⟪_⟫ᵐᵃ )
open import Classical.Small.Structures.Magma    using ( Magma ; opsToMagma )
import      Classical.Structures.Magma          as Polymorphic
```

#### <a id="the-table">The Cayley table and its operation</a>

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

#### <a id="the-magma">The magma `(Fin 4, _·_)`</a>

```agda
cim-magma : Magma
cim-magma = opsToMagma (Fin 4) _·_

open Polymorphic.Magma-Op cim-magma using ( _∙_ )
```

#### <a id="laws">Commutativity and idempotence</a>

Both laws are decidable over the finite carrier, so each is discharged by
`from-yes`{.AgdaFunction} applied to the corresponding decision from
[`Examples.Classical.Cayley`][].  No case dump is written by hand; if the table
violated a law the decision would reduce to `no`{.AgdaInductiveConstructor} and
the term would fail to type-check.

```agda
·-comm : ∀ a b → a · b ≡ b · a
·-comm = from-yes (Commutative? _·_)

·-idem : ∀ a → a · a ≡ a
·-idem = from-yes (Idempotent? _·_)
```

#### <a id="not-associative">The operation is not associative</a>

A single triple witnesses the failure of associativity: `(0 · 1) · 2`{.AgdaFunction}
reduces to `2`{.AgdaInductiveConstructor} while `0 · (1 · 2)`{.AgdaFunction}
reduces to `3`{.AgdaInductiveConstructor}.  So this magma is not a semigroup.

```agda
·-not-associative : ¬ (∀ a b c → (a · b) · c ≡ a · (b · c))
·-not-associative assoc with assoc 0F 1F 2F
... | ()
```

#### <a id="acceptance">Acceptance checks</a>

The `Magma-Op`{.AgdaModule} accessor interprets to the tabulated operation on the
nose, with no opacity from `opsToMagma`{.AgdaFunction} or the `Curry₂`{.AgdaFunction}
wrapping; discharged by `refl`{.AgdaInductiveConstructor}.

```agda
∙-is-·-ma : ∀ (a b : Fin 4) → a ∙ b ≡ a · b
∙-is-·-ma a b = refl
```

The bundle bridge round-trips on `cim-magma`{.AgdaFunction} pointwise, exactly as
for the other magma examples (per
[ADR-002 v2 §6](../../docs/adr/002-classical-layer-design.md)).

```agda
open Polymorphic.Magma-Op ⟪ ⟨ cim-magma ⟩ᵐᵃ ⟫ᵐᵃ using () renaming ( _∙_ to _·′_ )

roundtrip-cim-ma : ∀ (a b : Fin 4) → a ·′ b ≡ a · b
roundtrip-cim-ma a b = refl
```

--------------------------------------

<span style="float:left;">[← Examples.Classical.Cayley](Examples.Classical.Cayley.html)</span>

{% include UALib.Links.md %}
