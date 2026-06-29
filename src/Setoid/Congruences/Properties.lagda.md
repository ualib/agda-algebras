---
layout: default
file: "src/Setoid/Congruences/Properties.lagda.md"
title: "Setoid.Congruences.Properties module"
date: "2026-06-19"
author: "the agda-algebras development team"
---

### Distributive and modular congruence lattices

This is the [Setoid.Congruences.Properties][] module of the [Agda Universal Algebra Library][].

[Setoid.Congruences.CompleteLattice][] assembled the congruence lattice of an
algebra.  This module names two properties that lattice may have — being
**distributive** and being **modular** — which the Maltsev conditions of congruence
distributivity (Jónsson) and congruence modularity (Day) characterize by the
existence of terms ([Setoid.Varieties.MaltsevConditions][]).

As in [Setoid.Congruences.CompleteLattice][], the lattice equations are stated at the
**absorbing** relation level `𝐋 ℓ₀ = 𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ ⊔ ℓ₀`.  At this level the join
`_∨_` (whose codomain otherwise bumps the level to `𝒈 ℓ`) lands back at the level of
the meet `_∧_`, so both are operations on `Con 𝑨 (𝐋 ℓ₀)` and the equations type-check.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Congruences.Properties {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive  using () renaming ( Set to Type )
open import Level           using ( Level ; _⊔_ ) renaming (suc to lsuc)

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Setoid.Algebras.Basic          {𝑆 = 𝑆} using ( Algebra )
open import Setoid.Congruences.Basic       {𝑆 = 𝑆} using ( Con )
open import Setoid.Congruences.Lattice     {𝑆 = 𝑆} using ( _⊆_ ; _≑_ ; _∧_ )
open import Setoid.Congruences.Generation  {𝑆 = 𝑆} using ( _∨_ )
```

#### The absorbing relation level

```agda
-- The relation level at which both meet and join are operations on Con 𝑨.
Ł : Level → Level → Level → Level
Ł α ρ ℓ₀ = 𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ ⊔ ℓ₀
```

#### Congruence distributivity

An algebra `𝑨` is **congruence-distributive** (CD) when its congruence lattice
satisfies the distributive law `θ ∧ (φ ∨ ψ) ≑ (θ ∧ φ) ∨ (θ ∧ ψ)`.  (The reverse
containment half of this `≑` is automatic in any lattice; the distributive law is the
forward containment `θ ∧ (φ ∨ ψ) ⊆ (θ ∧ φ) ∨ (θ ∧ ψ)`, but we state the full
symmetric `≑` result for uniformity.)

```agda
module _ {α ρ : Level} (𝑨 : Algebra α ρ)(ℓ₀ : Level) where
  CongruenceDistributive : Type (lsuc (Ł α ρ ℓ₀))
  CongruenceDistributive = (θ φ ψ : Con 𝑨 (Ł α ρ ℓ₀)) → θ ∧ (φ ∨ ψ) ≑ (θ ∧ φ) ∨ (θ ∧ ψ)
```

#### Congruence modularity

An algebra `𝑨` is **congruence-modular** (CM) when its congruence lattice satisfies
the modular law: whenever `θ ⊆ ψ`, `θ ∨ (φ ∧ ψ) ≑ (θ ∨ φ) ∧ ψ`.  Distributivity
implies modularity, so the congruence-distributive algebras form a subclass of the
congruence-modular ones.

```agda
  CongruenceModular : Type (lsuc (Ł α ρ ℓ₀))
  CongruenceModular = (θ φ ψ : Con 𝑨 (Ł α ρ ℓ₀)) → θ ⊆ ψ → θ ∨ (φ ∧ ψ) ≑ (θ ∨ φ) ∧ ψ
```
