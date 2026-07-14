---
layout: default
file: "src/Classical/Signatures/Unary.lagda.md"
title: "Classical.Signatures.Unary module"
date: "2026-07-12"
author: "the agda-algebras development team"
---

### The signature of unary algebras

This is the [Classical.Signatures.Unary][] module of the [Agda Universal Algebra Library][].

A *unary algebra* over a set `A` of operation symbols is a carrier equipped with
one unary operation per element of `A`.  The most important examples are
**G-sets**: for a group `G`, an action of `G` on a set is exactly an algebra over
the unary signature whose symbol set is the carrier of `G` (satisfying the action
equations).  The two-layer congruence programme (ADR-008) uses this signature for
its coset algebras `G ↷ G/H`, whose congruence lattices realize the intervals
`[H, G]` of subgroup lattices.

Because a `Sig-Unary`-algebra is an `Algebra`{.AgdaRecord} like any other, the whole
congruence machinery (`Con`{.AgdaFunction}, quotients, homomorphism theorems) applies
to G-sets with no special cases.

The arity of every symbol is `Fin 1`, matching the convention of the unary symbol
`⁻¹-Op` in [`Sig-Group`][Classical.Signatures.Group].

This module deviates from the normative `Op-X`/`ar-X` pattern of
[Classical.Signatures.Magma][] in one respect, and deliberately so: the
operation-symbol type is a *parameter* `A`, not a fixed data type of named
constructors, so there is no `Op-Unary` data declaration and no pattern-matching
arity function.  The arity function is constantly `Fin 1` — the "recommended
shape" of [Examples.Setoid.FinitarySignatures][], under which every arity reduces
definitionally to a concrete `Fin`, so finiteness witnesses need no case split
(see `Classical.Signatures.Finite`).

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Signatures.Unary where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive using () renaming ( Set to Type )
open import Data.Fin.Base  using ( Fin )
open import Data.Product   using ( _,_ )
open import Level          using ( Level ; 0ℓ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Signatures using ( Signature )
```
-->

#### The signature value

One unary operation symbol per element of `A`.

```agda
Sig-Unary : {ℓ : Level} → Type ℓ → Signature ℓ 0ℓ
Sig-Unary A = A , λ _ → Fin 1
```

--------------------------------------
