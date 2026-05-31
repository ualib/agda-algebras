---
layout: default
file: "src/Examples/Classical/Cayley.lagda.md"
title: "Examples.Classical.Cayley module"
date: "2026-05-31"
author: "the agda-algebras development team"
---

### Cayley tables for finite operations

This is the [Examples.Classical.Cayley][] module of the [Agda Universal Algebra Library][].

A *Cayley table* (or *multiplication table*) specifies a binary operation on a
finite set by tabulating every product.  This module fixes the representation
the finite worked examples in this subtree share, and answers the practical
question: *what is a good way to describe a finite operation by its Cayley table
in Agda, and how does one then discharge the algebraic laws?*

The representation is a square table of indices.  We take the carrier to be the
canonical `n`-element type `Fin n`{.AgdaDatatype}, and a Cayley table to be an
`n × n` matrix of elements of `Fin n`{.AgdaDatatype}, stored row-major as a
`Vec`{.AgdaDatatype} of rows:

+  `⟦ t ⟧ a b`{.AgdaFunction} reads the entry in row `a`, column `b`.  This makes
   the table itself a first-class, inspectable datum — the literal you write down
   *is* the Cayley table — while `⟦_⟧`{.AgdaFunction} turns it into the
   `Op₂ (Fin n)`{.AgdaFunction} that the `Classical/`{.AgdaModule} builders expect.

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

module Examples.Classical.Cayley where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive          using () renaming ( Set to Type )
open import Algebra.Core            using ( Op₂ )
open import Data.Nat                using ( ℕ )
open import Data.Fin               using ( Fin )
open import Data.Fin.Properties     using ( _≟_ ; all? )
open import Data.Vec.Base           using ( Vec ; lookup )
open import Relation.Binary.PropositionalEquality  using ( _≡_ )
open import Relation.Nullary.Decidable.Core         using ( Dec )

-- Re-exported so the worked examples can discharge laws with a single name.
open import Relation.Nullary.Decidable.Core         using ( from-yes ) public
```

#### The table representation

```agda
-- An n × n Cayley table over the carrier Fin n, stored as a vector of rows.
Table : ℕ → Type
Table n = Vec (Vec (Fin n) n) n

-- Interpret a table as a binary operation: ⟦ t ⟧ a b is the row-a, column-b entry.
⟦_⟧ : ∀ {n} → Table n → Op₂ (Fin n)
⟦ t ⟧ a b = lookup (lookup t a) b
```

#### Decidable algebraic laws

Each law over the finite carrier is decidable; we expose the decision so that the
examples can extract the proof with `from-yes`{.AgdaFunction} whenever the table
satisfies the law.

```agda
module _ {n : ℕ} (_·_ : Op₂ (Fin n)) where

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

--------------------------------------

<span style="float:left;">[← Examples.Classical](Examples.Classical.html)</span>

{% include UALib.Links.md %}
