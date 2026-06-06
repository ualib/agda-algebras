---
layout: default
title : "Overture.Cayley module (The Agda Universal Algebra Library)"
date : "2026-05-31"
author: "the agda-algebras development team"
---

### Cayley tables for finite operations

This is the [Overture.Cayley][] module of the [Agda Universal Algebra Library][].

A *Cayley table* (or *multiplication table*) specifies a binary operation on a finite
set by tabulating every product.  This module fixes a small, reusable representation
for finite operations together with the decision procedures that discharge their
algebraic laws, and so answers the following practical question:

> How does one represent a binary operation on a finite set by its Cayley table in
> Agda, and how does one prove the laws of such an operation?

The representation deliberately depends only on the finite-data parts of the standard
library — `Fin`{.AgdaDatatype}, `Vec`{.AgdaDatatype}, and decidable equality on
`Fin n` — and does not depend on the standard library's algebra hierarchy.

A binary operation is just a function `Fin n → Fin n → Fin n`; we do not route it
through `Algebra.Core.Op₂` or any bundle.  The representation is a square table of
indices.  The carrier is the canonical `n`-element type `Fin n`, and a Cayley table
is an `n × n` array of elements of `Fin n`, stored row-major as a
`Vec`{.AgdaDatatype} of rows:

> `⟦ t ⟧ a b` reads the entry in row `a`, column `b`.  This makes the table itself a
> first-class, inspectable datum — the literal you write down *is* the Cayley table
> — while `⟦_⟧`{.AgdaFunction} turns it into the binary operation in
> `Fin n → Fin n → Fin n` that the `Classical`{.AgdaModule} builders
> (`opsToMagma`{.AgdaFunction}, `eqsToGroup`{.AgdaFunction}, …) consume.

The pay-off is that an equational law over a finite carrier is a *decidable*
proposition: `Fin n` has decidable equality, and `Data.Fin.Properties.all?` turns a
pointwise decision procedure into a decision for a universally quantified statement.
So each law (associativity, commutativity, idempotence, the identity and inverse
laws) is discharged by `from-yes`{.AgdaFunction} applied to the corresponding
decision, with no hand-written case dump.

Equivalently, if the table you wrote down does *not* satisfy a law, the decision
reduces to `no`{.AgdaInductiveConstructor} and the `from-yes`{.AgdaFunction} term
fails to type-check; in this way, the operation's properties can be checked by the
Agda type checker.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Overture.Cayley where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive                   using () renaming ( Set to Type )
open import Data.Nat                         using ( ℕ )
open import Data.Fin                         using ( Fin )
open import Data.Vec.Base                    using ( Vec ; lookup )

-- Re-exported so downstream examples can discharge laws with a single name.
open import Relation.Nullary.Decidable.Core  using ( from-yes ) public
```

#### The table representation

```agda
-- An n × n Cayley table over the carrier Fin n, stored as a vector of rows.
Table : ℕ → Type
Table n = Vec (Vec (Fin n) n) n

-- Interpret a table as a binary operation: ⟦ t ⟧ a b is the row-a, column-b entry.
⟦_⟧ : ∀ {n} → Table n → (Fin n → Fin n → Fin n)
⟦ t ⟧ a b = lookup (lookup t a) b
```

#### Decidable algebraic laws

The decidable equational-law checkers for finite operations — `Associative?`,
`Commutative?`, `Idempotent?`, the identity/inverse laws, and the two-operation
absorption and distributivity laws — live in [`Overture.Operations.Properties`][].
They take an arbitrary finite operation `Fin n → Fin n → Fin n` and do not touch the
table representation, so they are not specific to Cayley tables; finiteness is simply
what makes the laws decidable.  Together with the `Table`/`⟦_⟧` machinery here and
the re-exported `from-yes`{.AgdaFunction}, they let a finite example discharge its
defining equations without writing a single case by hand.

#### A note on the operation type

This module types a binary operation as a bare `Fin n → Fin n → Fin n` rather than
the library's tuple-indexed `Op`{.AgdaFunction}.  There is a single canonical,
arity-first `Op I A = (I → A) → A` in `Overture.Operations`{.AgdaModule}; although
that tuple-indexed shape is the right one for the universal-algebra meta-theory, it
is the wrong shape for a Cayley table.  A table is read in *curried* form (`⟦ t ⟧ a
b` is the row-`a`, column-`b` entry) and the `Classical`{.AgdaModule} builders
(`opsToMagma`{.AgdaFunction}, `eqsToGroup`{.AgdaFunction}, …) that consume
`⟦_⟧`{.AgdaFunction} take their binary operation curried as `Fin n → Fin n → Fin n`.
Routing `⟦_⟧`{.AgdaFunction} through the tuple-indexed `Op (Fin 2) (Fin n)` would
only insert `Curry₂`/`Uncurry₂` adapters at every call site and obscure the
two-dimensional table, so the finite Cayley-table case keeps the plain curried
function type.  The decidable-law checkers in [`Overture.Operations.Properties`][]
take the same bare `Fin n → Fin n → Fin n`, for the same reason: finiteness is what
makes the laws decidable, independently of how an operation's arguments are packaged.

--------------------------------------

<span style="float:left;">[← Overture.Operations](Overture.Operations.html)</span>

{% include UALib.Links.md %}
