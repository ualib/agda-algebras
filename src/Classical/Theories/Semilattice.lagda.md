---
layout: default
file: "src/Classical/Theories/Semilattice.lagda.md"
title: "Classical.Theories.Semilattice module"
date: "2026-05-27"
author: "the agda-algebras development team"
---

### The equational theory of semilattices

This is the [Classical.Theories.Semilattice][] module of the [Agda Universal Algebra Library][].

A semilattice is an idempotent commutative semigroup: its theory adds idempotency to
commutativity and associativity, over the same `Sig-Magma` signature (no new symbols).
`Th-Semilattice` therefore has three equations, all composed from the generic builders
of [`Classical.Equations`][].

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Theories.Semilattice where

open import Agda.Primitive                         using () renaming ( Set to Type )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Product                           using ( _×_ )
open import Relation.Binary.PropositionalEquality  using ( refl )

open import Classical.Signatures.Magma             using ( Sig-Magma ; ∙-Op )
open import Classical.Equations                    using ( Associative ; Commutative ; Idempotent )
open import Overture.Terms {𝑆 = Sig-Magma}         using ( Term )

data Eq-Semilattice : Type where
  assoc comm idem : Eq-Semilattice

Th-Semilattice : Eq-Semilattice → Term (Fin 3) × Term (Fin 3)
Th-Semilattice assoc = Associative ∙-Op refl 0F 1F 2F
Th-Semilattice comm  = Commutative ∙-Op refl 0F 1F
Th-Semilattice idem  = Idempotent  ∙-Op refl 0F
```

--------------------------------------

{% include UALib.Links.md %}
