---
layout: default
file: "src/Classical/Theories/Semigroup.lagda.md"
title: "Classical.Theories.Semigroup module"
date: "2026-05-18"
author: "the agda-algebras development team"
---

### The equational theory of semigroups

This is the [Classical.Theories.Semigroup][] module of the [Agda Universal Algebra Library][].

This is the first concrete equational theory module in the [`Classical/`][Classical]
tree, and as such this file's prose is normative for every subsequent
`Classical/Theories/X.lagda.md` (Monoid in M3-6, Group in M3-6, Lattice in M3-7,
Ring in M3-8).  See [ADR-002 v2 §3, §4](../../docs/adr/002-classical-layer-design.md)
for the design rationale.

The shape established here is:

+  An *index type* `Eq-<Structure> : Type` — a small named enum whose constructors
   correspond one-to-one with the defining equations of `<Structure>`'s theory.  For
   semigroups the index is the singleton enum `Eq-Semigroup` with sole constructor
   `assoc`.  Single-equation theories use a singleton enum rather than degenerating
   the index to `⊤`; the named constructor pays for itself in error-message
   readability and in symmetry with multi-equation theories landing later.
+  A *theory function* `Th-<Structure> : Eq-<Structure> → Term (Fin n) × Term (Fin n)`
   composed from the generic equation builders of [`Classical.Equations`][Classical.Equations] (M3-2)
   applied to the operation symbols of `Sig-<Structure>`.  The codomain is spelled
   in its long form rather than abbreviated to `_`, per the meta-resolution-pitfall
   note in [ADR-002 v2 §4](../../docs/adr/002-classical-layer-design.md).
+  The *variable carrier* is `Fin n` for the smallest `n` that suffices, per
   [ADR-002 v2 §2](../../docs/adr/002-classical-layer-design.md).  Associativity
   needs three distinct variables, so `n = 3` and the variable patterns at use
   sites are `0F`, `1F`, `2F` from `Data.Fin.Patterns`.

Since semigroups share the magma signature `Sig-Magma` — semigroups are precisely
those magmas whose binary operation is associative — there is no `Sig-Semigroup`.
The variable carrier `Fin 3` and the magma signature `Sig-Magma` together fully
parameterize the equation builder `Associative` from `Classical.Equations`.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Theories.Semigroup where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive                         using () renaming ( Set to Type )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Product                           using ( _×_ )
open import Relation.Binary.PropositionalEquality  using ( refl )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Signatures.Magma             using ( Sig-Magma ; ∙-Op )
open import Classical.Equations                    using ( Associative )
open import Overture.Terms {𝑆 = Sig-Magma}         using ( Term )
```
-->

#### The index of equations

Semigroup's theory has exactly one equation, associativity.  The singleton enum
`Eq-Semigroup` names it.

```agda
data Eq-Semigroup : Type where
  assoc : Eq-Semigroup
```

#### The theory map

`Th-Semigroup` sends the sole equation constructor `assoc` to the associativity
term-pair built by the generic `Associative` builder from
[`Classical.Equations`][Classical.Equations].  The arity-conformance evidence `refl` typechecks
because `ar-Magma ∙-Op` reduces definitionally to `Fin 2` — this is what the
`Classical/Signatures/Magma` arity-function-by-direct-pattern-matching convention
buys us.

```agda
Th-Semigroup : Eq-Semigroup → Term (Fin 3) × Term (Fin 3)
Th-Semigroup assoc = Associative ∙-Op refl 0F 1F 2F
```

Unfolded, `Th-Semigroup assoc` is the pair `((ℊ 0F ∙ ℊ 1F) ∙ ℊ 2F , ℊ 0F ∙ (ℊ 1F ∙ ℊ 2F))`
of `Sig-Magma`-terms over the variable carrier `Fin 3` — the left-associated and
right-associated three-fold product, respectively.
