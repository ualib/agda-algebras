---
layout: default
file: "src/FLRP/Closure/Basic.lagda.md"
title: "FLRP.Closure.Basic module (The Agda Universal Algebra Library)"
date: "2026-07-24"
author: "the agda-algebras development team"
---

### The closure toolkit for decidable representability

This is the [FLRP.Closure.Basic][] module of the [Agda Universal Algebra Library][].

The class of representable lattices is closed under a catalogue of operations.[^1]
This module is work package WP-5's umbrella over that catalogue at Layer D,
re-exporting the two proved closure theorems and deriving the rest:

+  **finite direct products**: `product-Representableᵈ`{.AgdaFunction}
   ([FLRP.Closure.Product][], after Tůma);
+  **ordinal sums**: `ordinalSum-Representableᵈ`{.AgdaFunction}
   ([FLRP.Closure.OrdinalSum][], after McKenzie and Snow); the *unglued* sum is
   the derived composite with `chain₂` glued in the middle;
+  **adjoining a new bottom or top**: `adjoinBottom-Representableᵈ`{.AgdaFunction}
   / `adjoinTop-Representableᵈ`{.AgdaFunction}, *corollaries* of ordinal-sum
   closure, obtained by instantiating one summand at the two-element chain (whose
   Layer-D representation `chain₂-Representableᵈ`{.AgdaFunction} is the
   constructive centerpiece of [FLRP.Representable][]);
+  **lattice duals**: `dual-Representableᵈ`{.AgdaFunction}, the Kurzweil–Netter
   duality theorem, proved in [FLRP.KurzweilNetter.Duality][] and consumed here
   through the simple-group package that parameterizes the proof with a finite
   nontrivial group together with the Kurzweil-surjectivity family, Entry 4 of
   [FLRP.Assumptions][]; Entry 2 of the registry (the duality theorem as an
   *imported* hypothesis) is retired; what remains classical is exactly Entry 4
   and the choice of a concrete nonabelian simple instantiation.

The payoff downstream: the two dual entries of the small-lattice census
(`L18` and `L22`, duals of the certified `SLR19` and `SLR23`) now rest on Entry 4
and an instantiation rather than on the full duality theorem; materializing those
conditional certificates remains computationally out of reach, since the
construction represents an `n`-element algebra's dual on `|S|ⁿ⁻¹ ≥ 60ⁿ⁻¹` elements.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.Closure.Basic where

-- Imports from the Agda Standard Library -----------------------------------
open import Data.Fin.Patterns                      using  ( 0F ; 1F )
open import Data.Product                           using  ( _,_ )
open import Level                                  using  ( 0ℓ )
open import Relation.Binary                        using  ( Setoid )
open import Relation.Binary.PropositionalEquality  using  ( refl )
open import Relation.Nullary                       using  ( ¬_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice              using  ( TopOf ; BottomOf )
open import Classical.Small.Structures.Lattice        using  ( Lattice )
open import Classical.Structures.Group.Basic          using  ( Group ; module Group-Op )
open import Classical.Structures.Lattice.Dual         using  ( dualLattice )
open import Classical.Structures.Lattice.OrdinalSum   using  ( ordinalSum )
open import FLRP.Assumptions                          using  ( KurzweilSurjectivityᵈAt )
open import FLRP.KurzweilNetter.Duality               using  ( module KurzweilNetterProof )
open import FLRP.Problem                              using  ( chain₂-lattice )
open import FLRP.Representable                        using  ( Representableᵈ
                                                             ; chain₂-Representableᵈ )
open import Setoid.Algebras.Basic                     using  ( 𝕌[_] ; 𝔻[_] )
open import Setoid.Algebras.Finite                    using  ( FiniteAlgebra )

open import FLRP.Closure.Product     public
open import FLRP.Closure.OrdinalSum  public
```
-->

#### Adjoining a new bottom or top

The two-element chain carries concrete extremum data: its top is `1` and its
bottom is `0`, each universal property decided by the four table entries.

```agda
chain₂-top : TopOf chain₂-lattice
chain₂-top = 1F , λ { 0F → refl ; 1F → refl }

chain₂-bot : BottomOf chain₂-lattice
chain₂-bot = 0F , λ { 0F → refl ; 1F → refl }
```

Adjoining a fresh extremum to a lattice is the special case of the glued ordinal
sum in which one summand is the two-element chain: gluing `chain₂`'s top onto
`𝑳`'s bottom leaves exactly one new element below everything (`adjoinBottom`), and
mirrored for `adjoinTop`.  Each is a one-application corollary of
`ordinalSum-Representableᵈ`{.AgdaFunction} at `chain₂-Representableᵈ`{.AgdaFunction},
confirming that the ordinal-sum statement carries no hidden nontriviality
assumptions on its summands.

```agda
-- Adjoin a new bottom: chain₂ glued below 𝑳, at 𝑳's chosen bottom.
adjoinBottom-Representableᵈ : {𝑳 : Lattice} (b : BottomOf 𝑳)
  → Representableᵈ 𝑳 → Representableᵈ (ordinalSum chain₂-lattice chain₂-top 𝑳 b)
adjoinBottom-Representableᵈ b r =
  ordinalSum-Representableᵈ chain₂-top b chain₂-Representableᵈ r

-- Adjoin a new top: chain₂ glued above 𝑳, at 𝑳's chosen top.
adjoinTop-Representableᵈ : {𝑳 : Lattice} (t : TopOf 𝑳)
  → Representableᵈ 𝑳 → Representableᵈ (ordinalSum 𝑳 t chain₂-lattice chain₂-bot)
adjoinTop-Representableᵈ t r =
  ordinalSum-Representableᵈ t chain₂-bot r chain₂-Representableᵈ
```

#### Duality

Here we prove closure under dualization (the Kurzweil–Netter theorem) using
[FLRP.KurzweilNetter.Duality][].  The parameters are the simple-group package of
the proof module: a finite group with a nontriviality witness and the
Kurzweil-surjectivity family in its decidable working form (Entry 4 of
[FLRP.Assumptions][], now a theorem: [FLRP.KurzweilSurjectivity][] proves the
family for any finite witnessed-nonabelian-simple base, and
[FLRP.KurzweilNetter.A5][] closes the composite at the certified `A₅`).

The parameterized form is kept so that census consumers can thread any base
group's package explicitly; a consumer wanting no package at all takes the
closed `kurzweilNetterDuality-A₅`{.AgdaFunction} instead.

```agda
module _ ((𝑺 , eqns) : Group 0ℓ 0ℓ) where
  open Setoid 𝔻[ 𝑺 ] using (_≈_)
  open Group-Op (𝑺 , eqns) using (ε)
  -- The Kurzweil–Netter closure, from the simple-group package of the proof.
  dual-Representableᵈ : (𝑭ₛ : FiniteAlgebra 𝑺) (s₀ : 𝕌[ 𝑺 ])
    → ¬ s₀ ≈ ε → (∀ n → KurzweilSurjectivityᵈAt (𝑺 , eqns) n)
    → (𝑳 : Lattice) → Representableᵈ 𝑳 → Representableᵈ (dualLattice 𝑳)
  dual-Representableᵈ 𝑭ₛ s₀ s₀≉ε surj =
    KurzweilNetterProof.kurzweilNetterDuality (𝑺 , eqns) 𝑭ₛ s₀ s₀≉ε surj
```

--------------------------------------


[^1]: See the roadmap's § 3; `docs/papers/fin-lat-rep/SmallLatticeReps.tex`, § Closure properties.
