---
layout: default
file: "src/Classical/Signatures/Semigroup.lagda.md"
title: "Classical.Signatures.Semigroup module"
date: "2026-05-15"
author: "the agda-algebras development team"
---

### <a id="classical-signatures-semigroup">Signature of semigroups</a>

This is the [Classical.Signatures.Semigroup][] module of the [Agda Universal Algebra Library][].

The semigroup signature `𝑆ₛₘ` has a single binary operation symbol.  Following the conventions established for the [`Classical/`][Classical] tree (see [ADR-002][ADR-002] and the module-header prose of [`Classical.Structures.Semigroup`][Classical.Structures.Semigroup]), the operation symbol is named via a one-constructor data type rather than encoded as `𝟙 → Fin 2`.  The constructor is `∙op` (the bare symbol `∙` is reserved for use-site infix sugar over `node`); the arity is `Fin 2`.  This pattern generalizes uniformly across the rest of the classical hierarchy: Monoid adds `eop`; Group adds `invop`; Lattice adds `∧op`, `∨op`; Ring adds five operators.

The named-constructor representation pays off twice: at proof-term inspection time, where `node ∙op …` self-documents the operation being applied (training-corpus value), and at definition time, where pattern matching on the constructor gives a clean recursion on the operations of a structure.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Signatures.Semigroup where

-- Imports from Agda and the Agda Standard Library -------------------------------
open import Agda.Primitive       using ()                 renaming ( Set to Type )
open import Data.Fin.Base        using ( Fin )
open import Data.Product         using ( _,_ )
open import Level                using ( 0ℓ )

-- Imports from agda-algebras ----------------------------------------------------
open import Overture.Signatures  using ( Signature )
```

The sort of operation symbols of `𝑆ₛₘ` is the one-constructor data type `Op-Semigroup`.

```agda
data Op-Semigroup : Type where
  ∙op : Op-Semigroup
```

The arity function sends the (unique) operation symbol `∙op` to the two-element index type `Fin 2`.  Choosing `Fin 2` rather than `𝟚`/`Bool` keeps the convention uniform with the rest of the classical hierarchy (where larger arities are inevitable for relational structures introduced later) and gives definitional reductions on `0F` and `1F` via stdlib's `Data.Fin.Patterns`.

```agda
ar-Semigroup : Op-Semigroup → Type
ar-Semigroup ∙op = Fin 2
```

Assembling these into a signature.

```agda
𝑆ₛₘ : Signature 0ℓ 0ℓ
𝑆ₛₘ = Op-Semigroup , ar-Semigroup
```

--------------------------------------

<span style="float:left;">[← Classical.Signatures](Classical.Signatures.html)</span>
<span style="float:right;">[Classical.Theories.Semigroup →](Classical.Theories.Semigroup.html)</span>

{% include UALib.Links.md %}
