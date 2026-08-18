---
layout: default
file: "src/Overture/Counting.lagda.md"
title: "Overture.Counting module"
date: "2026-08-17"
author: "the agda-algebras development team"
---

### Counting by filtering

This is the [Overture.Counting][] module of the [Agda Universal Algebra Library][].

Several finiteness arguments in the library measure a subobject of a finite structure by
*counting*: fix a list of candidates, filter it by a decidable membership test, and take
the length.  The measure is used the same way each time — a containment makes it
monotone, and a containment that misses a listed element makes it strictly smaller —
so the two facts are proved once here, for an arbitrary type and an arbitrary pair of
decidable predicates, and instantiated downstream.

Two consumers so far, both descending on such a measure through
`<`-well-foundedness: the maximal-congruence search of
[Setoid.Subalgebras.Subdirect.Finite][], whose candidates are the pairs of enumerated
carrier elements, and the minimal-normal descent of
[Classical.Structures.Group.MinimalNormalDescent][], whose candidates are the enumerated
elements themselves.

The module is signature- and setoid-agnostic — it mentions only `List`{.AgdaDatatype},
`Dec`{.AgdaDatatype}, and `ℕ`{.AgdaDatatype} — which is why it lands in
[Overture][] rather than beside either consumer.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Overture.Counting where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -----------------------------------
open import Data.Empty                          using  ( ⊥-elim )
open import Data.List.Base                      using  ( List ; [] ; _∷_
                                                       ; filter ; length )
open import Data.List.Membership.Propositional  using  ( _∈_ )
open import Data.List.Relation.Unary.Any        using  ( here ; there )
open import Data.Nat.Base                       using  ( _≤_ ; _<_ ; z≤n ; s≤s )
open import Data.Nat.Properties                 using  ( m≤n⇒m≤1+n ; n<1+n ; <-trans )
open import Level                               using  ( Level )
open import Relation.Nullary                    using  ( ¬_ ; Dec ; yes ; no )

open import Relation.Binary.PropositionalEquality using ( refl )

private variable ℓ₁ ℓ₂ ℓ₃ : Level
```
-->

#### The two lemmas

Fix a type `X`{.AgdaBound}, two decidable predicates on it, and a proof that the first
entails the second.

```agda
module _ {X : Type ℓ₁}{P : X → Type ℓ₂}{Q : X → Type ℓ₃}
         (P? : (x : X) → Dec (P x))(Q? : (x : X) → Dec (Q x))
         (sub : ∀ {x} → P x → Q x) where

  -- If P entails Q then no more elements pass the P-filter than the Q-filter.
  filter-length-mono : (xs : List X) → length (filter P? xs) ≤ length (filter Q? xs)
  filter-length-mono [] = z≤n
  filter-length-mono (x ∷ xs) with P? x | Q? x
  ... | yes _  | yes _  = s≤s (filter-length-mono xs)
  ... | yes px | no ¬qx = ⊥-elim (¬qx (sub px))
  ... | no _   | yes _  = m≤n⇒m≤1+n (filter-length-mono xs)
  ... | no _   | no _   = filter-length-mono xs

  -- If moreover some w ∈ xs has Q w and ¬ P w, the P-filter is strictly shorter.
  filter-length-strict : (xs : List X){w : X} → w ∈ xs → Q w → ¬ P w
                       → length (filter P? xs) < length (filter Q? xs)
  filter-length-strict (x ∷ xs) (here refl) qw ¬pw with P? x | Q? x
  ... | yes pw | _      = ⊥-elim (¬pw pw)
  ... | no _   | yes _  = s≤s (filter-length-mono xs)
  ... | no _   | no ¬qw = ⊥-elim (¬qw qw)
  filter-length-strict (x ∷ xs) (there w∈xs) qw ¬pw with P? x | Q? x
  ... | yes _  | yes _  = s≤s (filter-length-strict xs w∈xs qw ¬pw)
  ... | yes px | no ¬qx = ⊥-elim (¬qx (sub px))
  ... | no _   | yes _  = <-trans (filter-length-strict xs w∈xs qw ¬pw) (n<1+n _)
  ... | no _   | no _   = filter-length-strict xs w∈xs qw ¬pw
```

--------------------------------------
