---
layout: default
title : "Setoid.Varieties.Invariants module (The Agda Universal Algebra Library)"
date : "2026-05-10"
author: "agda-algebras development team"
---

### Algebraic invariants for setoid algebras

This is the [Setoid.Varieties.Invariants][] module of the [Agda Universal Algebra Library][].

A property `P` of (setoid) algebras is called an **algebraic invariant** when it is stable under isomorphism: whenever `𝑨 ≅ 𝑩`, the proposition `P 𝑨` implies `P 𝑩`.  Equivalently, an algebraic invariant is a predicate that factors through the isomorphism-type of `𝑨` — a property of the algebra qua structure, independent of its concrete carrier.  The notion is the foundational guard rail of universal algebra: the structurally meaningful properties of an algebra (satisfying an identity, being subdirectly irreducible, generating a given variety, being free over a set of generators, and so on) are all algebraic invariants, and a property that fails to be invariant is, almost by definition, not a property of the algebra but of one particular presentation of it.

The canonical example available in this library is the modelling relation `𝑨 ⊧ (p ≈̇ q)`.  Its algebraic invariance is the content of [`Setoid.Varieties.Properties.⊧-I-invar`][], which states precisely that `λ 𝑨 → 𝑨 ⊧ (p ≈̇ q)` satisfies the `AlgebraicInvariant` predicate defined below.  More generally, each closure operator `H`, `S`, `P`, `V` of the variety theory is built from operations that respect `_≅_`, so class membership `_∈ H 𝒦`, `_∈ S 𝒦`, `_∈ P 𝒦`, and `_∈ V 𝒦` is itself an algebraic invariant.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Varieties.Invariants {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library --------------------------------
open import Agda.Primitive  using () renaming ( Set to Type )
open import Level           using ( Level )
open import Relation.Unary  using ( Pred )

-- Imports from the Agda Universal Algebra Library -------------------------------
open import Setoid.Algebras       {𝑆 = 𝑆}  using ( Algebra )
open import Setoid.Homomorphisms  {𝑆 = 𝑆}  using ( _≅_ )

private variable α ρᵃ ℓ : Level
```

A predicate `P : Pred (Algebra α ρᵃ) ℓ` is an *algebraic invariant* when, given any two algebras `𝑨` and `𝑩` at the same universe levels and an isomorphism `𝑨 ≅ 𝑩`, the property `P 𝑨` entails `P 𝑩`.  The same-level restriction is forced by Agda's `Pred` type and matches the legacy `Base.Varieties.Invariants` definition; a level-heterogeneous variant could be obtained by parametrizing over a level-indexed family of predicates, but no current consumer requires it.

```agda
AlgebraicInvariant : Pred (Algebra α ρᵃ) ℓ → Type _
AlgebraicInvariant P = ∀ 𝑨 𝑩 → P 𝑨 → 𝑨 ≅ 𝑩 → P 𝑩
```

--------------------------------

<span style="float:left;">[← Setoid.Varieties.Properties](Setoid.Varieties.Properties.html)</span>
<span style="float:right;">[Setoid.Varieties.Preservation →](Setoid.Varieties.Preservation.html)</span>

{% include UALib.Links.md %}
