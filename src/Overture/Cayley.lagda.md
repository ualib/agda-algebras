---
layout: default
title : "Overture.Cayley module (The Agda Universal Algebra Library)"
date : "2026-05-31"
author: "the agda-algebras development team"
---

### Cayley tables for finite operations

This is the [Overture.Cayley][] module of the [Agda Universal Algebra Library][].

A *Cayley table* (or *multiplication table*) specifies a binary operation on a
finite set by tabulating every product.  This module fixes a small, reusable
representation for finite operations together with the decision procedures that
discharge their algebraic laws, and so answers the practical question: *what is a
good way to describe a finite operation by its Cayley table in Agda, and how does
one then prove the laws?*

The representation deliberately depends only on the finite-data parts of the
standard library — `Fin`{.AgdaDatatype}, `Vec`{.AgdaDatatype}, and decidable
equality on `Fin n`{.AgdaDatatype} — and **not** on the standard library's
algebra hierarchy.  A binary operation is just a function
`Fin n → Fin n → Fin n`{.AgdaFunction}; we do not route it through
`Algebra.Core.Op₂`{.AgdaFunction} or any bundle.  (Re-expressing finite
operations over the library's own tuple-indexed `Op`{.AgdaFunction} is deferred
to the milestone-4 cleanup that consolidates the two `Op`{.AgdaFunction}
declarations; see the note at the end of this module.)

The representation is a square table of indices.  The carrier is the canonical
`n`-element type `Fin n`{.AgdaDatatype}, and a Cayley table is an `n × n` matrix
of elements of `Fin n`{.AgdaDatatype}, stored row-major as a `Vec`{.AgdaDatatype}
of rows:

+  `⟦ t ⟧ a b`{.AgdaFunction} reads the entry in row `a`, column `b`.  This makes
   the table itself a first-class, inspectable datum — the literal you write down
   *is* the Cayley table — while `⟦_⟧`{.AgdaFunction} turns it into the binary
   operation `Fin n → Fin n → Fin n`{.AgdaFunction} that the `Classical/`{.AgdaModule}
   builders (`opsToMagma`{.AgdaFunction}, `eqsToGroup`{.AgdaFunction}, …) consume.

The pay-off is that an equational law over a finite carrier is a *decidable*
proposition: `Fin n`{.AgdaDatatype} has decidable equality, and
[`Data.Fin.Properties.all?`][] turns a pointwise decision procedure into a
decision for a universally quantified statement.  So each law — associativity,
commutativity, idempotence, the identity and inverse laws — is discharged by
`from-yes`{.AgdaFunction} applied to the corresponding decision, with no
hand-written case dump.  Equivalently: if the table you wrote down does *not*
satisfy a law, the decision reduces to `no`{.AgdaInductiveConstructor} and the
`from-yes`{.AgdaFunction} term fails to type-check, so the table is checked for
you at compile time.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Overture.Cayley where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive          using () renaming ( Set to Type )
open import Data.Nat                using ( ℕ )
open import Data.Fin               using ( Fin )
open import Data.Fin.Properties     using ( _≟_ ; all? )
open import Data.Vec.Base           using ( Vec ; lookup )
open import Relation.Binary.PropositionalEquality  using ( _≡_ )
open import Relation.Nullary.Decidable.Core         using ( Dec )

-- Re-exported so downstream examples can discharge laws with a single name.
open import Relation.Nullary.Decidable.Core         using ( from-yes ) public
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

Each law over the finite carrier is decidable; we expose the decision so that
callers can extract the proof with `from-yes`{.AgdaFunction} whenever the
operation satisfies the law.  These checkers are stated for an arbitrary binary
operation `Fin n → Fin n → Fin n`{.AgdaFunction}, so they apply to any finite
operation, not only to table-defined ones.

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

#### A note on the operation type

This module types a binary operation as a bare `Fin n → Fin n → Fin n`{.AgdaFunction}
rather than the library's tuple-indexed `Op`{.AgdaFunction}.  That is a
deliberate, temporary choice: the library currently carries *two* declarations
of `Op`{.AgdaFunction} — `Overture.Operations.Op A I`{.AgdaFunction} (carrier
first) and `Classical.Operations.Op I A`{.AgdaFunction} (arity first) — and the
right fix is to consolidate them into a single canonical `Op`{.AgdaFunction} in
`Overture.Operations`{.AgdaModule} before threading it through new constructions.
That consolidation has a wide blast radius and is tracked as a milestone-4 style
sweep; once it lands, `⟦_⟧`{.AgdaFunction} and the checkers above can be
re-expressed over the canonical `Op`{.AgdaFunction} if that reads better.

--------------------------------------

<span style="float:left;">[← Overture.Operations](Overture.Operations.html)</span>

{% include UALib.Links.md %}
