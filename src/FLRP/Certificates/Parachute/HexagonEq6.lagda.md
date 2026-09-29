---
layout: default
file: "src/FLRP/Certificates/Parachute/HexagonEq6.lagda.md"
title: "FLRP.Certificates.Parachute.HexagonEq6 module (The Agda Universal Algebra Library)"
date: "2026-09-28"
author: "the agda-algebras development team (emitted by scripts/python/flrp)"
---

### A machine-checked representation: Con(hexagon closure witness on 6 points, a generating set of the preserving monoid) ≅ P(3,3): parachute of two three-chains

This is the [FLRP.Certificates.Parachute.HexagonEq6][] module of the [Agda Universal Algebra Library][].

**This module was emitted by `scripts/python/flrp/emit_agda.py` from
`scripts/python/flrp/inputs/hexagon_eq6.json`.  Do not edit it by hand; rerun the emitter instead.**

The hexagon P(3,3), the parachute of two three-element chains, as the congruence lattice of a six-element unary algebra. The Eq(6) closure search of issue #578 found one closed class, the chains 012|34|5 < 012|345 and 03|15|2|4 < 03|15|24; the witness is the monoid of the 45 unary maps preserving those four partitions, and the operations below are a generating set of it, so the congruence lattice is the same. Its smallest known carrier as a group interval has order 25920 (U4(2), index 1080), and no group of order at most 300 carries it core-freely: the congruence-lattice question and the group-interval question live at different scales.

It re-verifies, end-to-end through the WP-6 certificate pipeline (#457), the
claim that the congruence lattice of the algebra "hexagon closure witness on 6 points, a generating set of the preserving monoid" — carrier size
6, unary operations `u0`, `u1`, `u2`, `u3` — is isomorphic to the lattice
"P(3,3): parachute of two three-chains" (6 elements).  The engine's output below (normal-form
parent vectors, Freese traces, and pointer tables) is certificate data only:
the search-free checkers of [Setoid.Congruences.Certificates][] re-verify all
of it during type-checking, and the [FLRP.Certificates][] assembly turns the
checked certificate into the headline theorems — a
`Representableᵈ`{.AgdaRecord} witness for the target lattice and a
`FiniteCongruencesᵈ`{.AgdaRecord} instance for the algebra.  Nothing is
believed on the engine's authority: a wrong table or trace would make a
decidable check compute to `no`{.AgdaInductiveConstructor} and break
compilation.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.Certificates.Parachute.HexagonEq6 where

-- Imports from Agda and the Agda Standard Library -----------------------------
open import Data.Fin.Base       using ( Fin )
open import Data.Fin.Patterns   using ( 0F ; 1F ; 2F ; 3F ; 4F ; 5F )
open import Data.List.Base      using ( [] ; _∷_ )
open import Data.Vec.Base       using ( Vec ; [] ; _∷_ )
open import Level               using ( 0ℓ )

-- Imports from the Agda Universal Algebra Library -----------------------------
open import Classical.Signatures.Unary   using ( Sig-Unary )
open import Classical.Structures.Unary   using ( tablesToUnaryAlgebra
                                               ; tablesToUnaryAlgebra-FiniteAlgebra
                                               ; Sig-Unary-Fin-FiniteSignature )
open import FLRP.Certificates            using ( MeetMatches ; meetMatches?
                                               ; certRepresentableᵈ )
open import FLRP.Problem                 using ( FiniteLattice ; toLattice )
open import FLRP.Representable           using ( Representableᵈ )
open import Overture.Cayley              using ( Table ; ⟦_⟧ ; from-yes )
open import Overture.Operations.Properties
                                         using ( Associative? ; Commutative?
                                               ; Idempotent? ; Absorbsˡ? ; Absorbsʳ? )
open import Setoid.Algebras.Basic        using ( Algebra )
open import Setoid.Algebras.Finite       using ( FiniteAlgebra )
open import Setoid.Congruences.Certificates.Schema
                                         using ( ParentVec ; Trace ; LatticeCert
                                               ; mkLatticeCert ; mkMerge
                                               ; seed ; translate )
open import Setoid.Congruences.Certificates.Congruence
                                         using ( module CertCheck )
open import Setoid.Congruences.Certificates.Lattice
                                         using ( module LatticeCheck )
open import Setoid.Congruences.Finite.Decidable
                                         using ( FiniteCongruencesᵈ )
open import Setoid.Signatures.Finite     using ( FiniteSignature )
```
-->

#### The algebra, from its operation tables

Row `f` of `opTables`{.AgdaFunction} is the value table of the `f`-th unary
operation; [Classical.Structures.Unary][] turns the table into the algebra
and its finiteness witnesses.

```agda
opTables : Vec (Vec (Fin 6) 6) 4
opTables = (0F ∷ 2F ∷ 1F ∷ 0F ∷ 1F ∷ 2F ∷ [])
         ∷ (1F ∷ 0F ∷ 1F ∷ 5F ∷ 5F ∷ 3F ∷ [])
         ∷ (1F ∷ 0F ∷ 2F ∷ 1F ∷ 2F ∷ 0F ∷ [])
         ∷ (3F ∷ 3F ∷ 4F ∷ 0F ∷ 2F ∷ 0F ∷ [])
         ∷ []

𝑨 : Algebra {𝑆 = Sig-Unary (Fin 4)} 0ℓ 0ℓ
𝑨 = tablesToUnaryAlgebra 6 4 opTables

𝑭 : FiniteAlgebra 𝑨
𝑭 = tablesToUnaryAlgebra-FiniteAlgebra 6 4 opTables

𝑺 : FiniteSignature (Sig-Unary (Fin 4))
𝑺 = Sig-Unary-Fin-FiniteSignature 4
```

#### The target lattice, from its Cayley tables

The claimed congruence lattice "P(3,3): parachute of two three-chains", presented exactly as the
worked lattice examples are ([Examples.Classical.Lattices.L7][]): meet and
join tables, every law discharged by decision over the finite carrier.

```agda
∧-table ∨-table : Table 6
∧-table = (0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ [])
        ∷ (0F ∷ 1F ∷ 1F ∷ 0F ∷ 0F ∷ 1F ∷ [])
        ∷ (0F ∷ 1F ∷ 2F ∷ 0F ∷ 0F ∷ 2F ∷ [])
        ∷ (0F ∷ 0F ∷ 0F ∷ 3F ∷ 3F ∷ 3F ∷ [])
        ∷ (0F ∷ 0F ∷ 0F ∷ 3F ∷ 4F ∷ 4F ∷ [])
        ∷ (0F ∷ 1F ∷ 2F ∷ 3F ∷ 4F ∷ 5F ∷ [])
        ∷ []

∨-table = (0F ∷ 1F ∷ 2F ∷ 3F ∷ 4F ∷ 5F ∷ [])
        ∷ (1F ∷ 1F ∷ 2F ∷ 5F ∷ 5F ∷ 5F ∷ [])
        ∷ (2F ∷ 2F ∷ 2F ∷ 5F ∷ 5F ∷ 5F ∷ [])
        ∷ (3F ∷ 5F ∷ 5F ∷ 3F ∷ 4F ∷ 5F ∷ [])
        ∷ (4F ∷ 5F ∷ 5F ∷ 4F ∷ 4F ∷ 5F ∷ [])
        ∷ (5F ∷ 5F ∷ 5F ∷ 5F ∷ 5F ∷ 5F ∷ [])
        ∷ []

open FiniteLattice

𝑳 : FiniteLattice
𝑳 .size     = 5
𝑳 ._∧_      = ⟦ ∧-table ⟧
𝑳 ._∨_      = ⟦ ∨-table ⟧
𝑳 .∧-assoc  = from-yes (Associative? ⟦ ∧-table ⟧)
𝑳 .∧-comm   = from-yes (Commutative? ⟦ ∧-table ⟧)
𝑳 .∧-idem   = from-yes (Idempotent? ⟦ ∧-table ⟧)
𝑳 .∨-assoc  = from-yes (Associative? ⟦ ∨-table ⟧)
𝑳 .∨-comm   = from-yes (Commutative? ⟦ ∨-table ⟧)
𝑳 .∨-idem   = from-yes (Idempotent? ⟦ ∨-table ⟧)
𝑳 .absorbˡ  = from-yes (Absorbsˡ? ⟦ ∧-table ⟧ ⟦ ∨-table ⟧)
𝑳 .absorbʳ  = from-yes (Absorbsʳ? ⟦ ∧-table ⟧ ⟦ ∨-table ⟧)
```

#### The certificate

The engine's whole-lattice certificate (design note § 4): the congruence
list as normal-form parent vectors, indexed by the lattice's carrier; the
principal-congruence pointer table with one Freese trace per carrier pair;
and the join traces, seeded by forest edges.  The meet and join tables are
the target's own tables, which is what `MeetMatches`{.AgdaFunction} pins.

```agda
open CertCheck 𝑭 𝑺 using ( arOf )

cert : LatticeCert 6 4 arOf 6
cert = mkLatticeCert partsᵛ 0F prinᵛ prinTrᵛ ∧-table ∨-table joinTrᵛ
  where
  partsᵛ : Vec (ParentVec 6) 6
  partsᵛ = (0F ∷ 1F ∷ 2F ∷ 3F ∷ 4F ∷ 5F ∷ [])
         ∷ (0F ∷ 0F ∷ 0F ∷ 3F ∷ 3F ∷ 5F ∷ [])
         ∷ (0F ∷ 0F ∷ 0F ∷ 3F ∷ 3F ∷ 3F ∷ [])
         ∷ (0F ∷ 1F ∷ 2F ∷ 0F ∷ 4F ∷ 1F ∷ [])
         ∷ (0F ∷ 1F ∷ 2F ∷ 0F ∷ 2F ∷ 1F ∷ [])
         ∷ (0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ [])
         ∷ []

  prinᵛ : Vec (Vec (Fin 6) 6) 6
  prinᵛ = (0F ∷ 1F ∷ 1F ∷ 3F ∷ 5F ∷ 5F ∷ [])
        ∷ (1F ∷ 0F ∷ 1F ∷ 5F ∷ 5F ∷ 3F ∷ [])
        ∷ (1F ∷ 1F ∷ 0F ∷ 5F ∷ 4F ∷ 5F ∷ [])
        ∷ (3F ∷ 5F ∷ 5F ∷ 0F ∷ 1F ∷ 2F ∷ [])
        ∷ (5F ∷ 5F ∷ 4F ∷ 1F ∷ 0F ∷ 2F ∷ [])
        ∷ (5F ∷ 3F ∷ 5F ∷ 2F ∷ 2F ∷ 0F ∷ [])
        ∷ []

  prinTrᵛ : Vec (Vec (Trace 6 4 arOf) 6) 6
  prinTrᵛ = ( []
            ∷ ( mkMerge 0F 1F (seed 0)
              ∷ mkMerge 0F 2F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 3F 4F (translate 3F 0F (0F ∷ []) 0)
              ∷ [] )
            ∷ ( mkMerge 0F 2F (seed 0)
              ∷ mkMerge 0F 1F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 3F 4F (translate 3F 0F (0F ∷ []) 1)
              ∷ [] )
            ∷ ( mkMerge 0F 3F (seed 0)
              ∷ mkMerge 1F 5F (translate 1F 0F (0F ∷ []) 0)
              ∷ [] )
            ∷ ( mkMerge 0F 4F (seed 0)
              ∷ mkMerge 0F 1F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 1F 5F (translate 1F 0F (0F ∷ []) 1)
              ∷ mkMerge 1F 2F (translate 2F 0F (0F ∷ []) 2)
              ∷ mkMerge 3F 2F (translate 3F 0F (0F ∷ []) 3)
              ∷ [] )
            ∷ ( mkMerge 0F 5F (seed 0)
              ∷ mkMerge 0F 2F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 1F 3F (translate 1F 0F (0F ∷ []) 1)
              ∷ mkMerge 1F 0F (translate 2F 0F (0F ∷ []) 2)
              ∷ mkMerge 3F 4F (translate 3F 0F (0F ∷ []) 2)
              ∷ [] )
            ∷ [] )
          ∷ ( ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 4F 3F (translate 3F 0F (0F ∷ []) 0)
              ∷ [] )
            ∷ []
            ∷ ( mkMerge 1F 2F (seed 0)
              ∷ mkMerge 0F 1F (translate 1F 0F (0F ∷ []) 0)
              ∷ mkMerge 3F 4F (translate 3F 0F (0F ∷ []) 1)
              ∷ [] )
            ∷ ( mkMerge 1F 3F (seed 0)
              ∷ mkMerge 2F 0F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 0F 5F (translate 1F 0F (0F ∷ []) 1)
              ∷ mkMerge 0F 1F (translate 2F 0F (0F ∷ []) 2)
              ∷ mkMerge 4F 3F (translate 3F 0F (0F ∷ []) 2)
              ∷ [] )
            ∷ ( mkMerge 1F 4F (seed 0)
              ∷ mkMerge 2F 1F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 0F 5F (translate 1F 0F (0F ∷ []) 1)
              ∷ mkMerge 0F 2F (translate 2F 0F (0F ∷ []) 2)
              ∷ mkMerge 3F 2F (translate 3F 0F (0F ∷ []) 3)
              ∷ [] )
            ∷ ( mkMerge 1F 5F (seed 0)
              ∷ mkMerge 0F 3F (translate 1F 0F (0F ∷ []) 0)
              ∷ [] )
            ∷ [] )
          ∷ ( ( mkMerge 2F 0F (seed 0)
              ∷ mkMerge 1F 0F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 4F 3F (translate 3F 0F (0F ∷ []) 1)
              ∷ [] )
            ∷ ( mkMerge 2F 1F (seed 0)
              ∷ mkMerge 1F 0F (translate 1F 0F (0F ∷ []) 0)
              ∷ mkMerge 4F 3F (translate 3F 0F (0F ∷ []) 1)
              ∷ [] )
            ∷ []
            ∷ ( mkMerge 2F 3F (seed 0)
              ∷ mkMerge 1F 0F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 1F 5F (translate 1F 0F (0F ∷ []) 1)
              ∷ mkMerge 2F 1F (translate 2F 0F (0F ∷ []) 2)
              ∷ mkMerge 4F 0F (translate 3F 0F (0F ∷ []) 3)
              ∷ [] )
            ∷ ( mkMerge 2F 4F (seed 0)
              ∷ mkMerge 1F 5F (translate 1F 0F (0F ∷ []) 0)
              ∷ mkMerge 0F 3F (translate 1F 0F (0F ∷ []) 0)
              ∷ [] )
            ∷ ( mkMerge 2F 5F (seed 0)
              ∷ mkMerge 1F 2F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 1F 3F (translate 1F 0F (0F ∷ []) 1)
              ∷ mkMerge 2F 0F (translate 2F 0F (0F ∷ []) 2)
              ∷ mkMerge 4F 0F (translate 3F 0F (0F ∷ []) 3)
              ∷ [] )
            ∷ [] )
          ∷ ( ( mkMerge 3F 0F (seed 0)
              ∷ mkMerge 5F 1F (translate 1F 0F (0F ∷ []) 0)
              ∷ [] )
            ∷ ( mkMerge 3F 1F (seed 0)
              ∷ mkMerge 0F 2F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 5F 0F (translate 1F 0F (0F ∷ []) 1)
              ∷ mkMerge 1F 0F (translate 2F 0F (0F ∷ []) 2)
              ∷ mkMerge 3F 4F (translate 3F 0F (0F ∷ []) 2)
              ∷ [] )
            ∷ ( mkMerge 3F 2F (seed 0)
              ∷ mkMerge 0F 1F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 5F 1F (translate 1F 0F (0F ∷ []) 1)
              ∷ mkMerge 1F 2F (translate 2F 0F (0F ∷ []) 2)
              ∷ mkMerge 0F 4F (translate 3F 0F (0F ∷ []) 3)
              ∷ [] )
            ∷ []
            ∷ ( mkMerge 3F 4F (seed 0)
              ∷ mkMerge 0F 1F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 1F 2F (translate 2F 0F (0F ∷ []) 1)
              ∷ [] )
            ∷ ( mkMerge 3F 5F (seed 0)
              ∷ mkMerge 0F 2F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 1F 0F (translate 2F 0F (0F ∷ []) 1)
              ∷ mkMerge 3F 4F (translate 3F 0F (0F ∷ []) 1)
              ∷ [] )
            ∷ [] )
          ∷ ( ( mkMerge 4F 0F (seed 0)
              ∷ mkMerge 1F 0F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 5F 1F (translate 1F 0F (0F ∷ []) 1)
              ∷ mkMerge 2F 1F (translate 2F 0F (0F ∷ []) 2)
              ∷ mkMerge 2F 3F (translate 3F 0F (0F ∷ []) 3)
              ∷ [] )
            ∷ ( mkMerge 4F 1F (seed 0)
              ∷ mkMerge 1F 2F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 5F 0F (translate 1F 0F (0F ∷ []) 1)
              ∷ mkMerge 2F 0F (translate 2F 0F (0F ∷ []) 2)
              ∷ mkMerge 2F 3F (translate 3F 0F (0F ∷ []) 3)
              ∷ [] )
            ∷ ( mkMerge 4F 2F (seed 0)
              ∷ mkMerge 5F 1F (translate 1F 0F (0F ∷ []) 0)
              ∷ mkMerge 3F 0F (translate 1F 0F (0F ∷ []) 0)
              ∷ [] )
            ∷ ( mkMerge 4F 3F (seed 0)
              ∷ mkMerge 1F 0F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 2F 1F (translate 2F 0F (0F ∷ []) 1)
              ∷ [] )
            ∷ []
            ∷ ( mkMerge 4F 5F (seed 0)
              ∷ mkMerge 1F 2F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 5F 3F (translate 1F 0F (0F ∷ []) 1)
              ∷ mkMerge 2F 0F (translate 2F 0F (0F ∷ []) 2)
              ∷ [] )
            ∷ [] )
          ∷ ( ( mkMerge 5F 0F (seed 0)
              ∷ mkMerge 2F 0F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 3F 1F (translate 1F 0F (0F ∷ []) 1)
              ∷ mkMerge 0F 1F (translate 2F 0F (0F ∷ []) 2)
              ∷ mkMerge 4F 3F (translate 3F 0F (0F ∷ []) 2)
              ∷ [] )
            ∷ ( mkMerge 5F 1F (seed 0)
              ∷ mkMerge 3F 0F (translate 1F 0F (0F ∷ []) 0)
              ∷ [] )
            ∷ ( mkMerge 5F 2F (seed 0)
              ∷ mkMerge 2F 1F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 3F 1F (translate 1F 0F (0F ∷ []) 1)
              ∷ mkMerge 0F 2F (translate 2F 0F (0F ∷ []) 2)
              ∷ mkMerge 0F 4F (translate 3F 0F (0F ∷ []) 3)
              ∷ [] )
            ∷ ( mkMerge 5F 3F (seed 0)
              ∷ mkMerge 2F 0F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 0F 1F (translate 2F 0F (0F ∷ []) 1)
              ∷ mkMerge 4F 3F (translate 3F 0F (0F ∷ []) 1)
              ∷ [] )
            ∷ ( mkMerge 5F 4F (seed 0)
              ∷ mkMerge 2F 1F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 3F 5F (translate 1F 0F (0F ∷ []) 1)
              ∷ mkMerge 0F 2F (translate 2F 0F (0F ∷ []) 2)
              ∷ [] )
            ∷ []
            ∷ [] )
          ∷ []

  joinTrᵛ : Vec (Vec (Trace 6 4 arOf) 6) 6
  joinTrᵛ = ( []
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 4F 3F (seed 2)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 4F 3F (seed 2)
              ∷ mkMerge 5F 3F (seed 3)
              ∷ [] )
            ∷ ( mkMerge 3F 0F (seed 0)
              ∷ mkMerge 5F 1F (seed 1)
              ∷ [] )
            ∷ ( mkMerge 3F 0F (seed 0)
              ∷ mkMerge 4F 2F (seed 1)
              ∷ mkMerge 5F 1F (seed 2)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 3F 0F (seed 2)
              ∷ mkMerge 4F 0F (seed 3)
              ∷ mkMerge 5F 0F (seed 4)
              ∷ [] )
            ∷ [] )
          ∷ ( ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 4F 3F (seed 2)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 4F 3F (seed 2)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 4F 3F (seed 2)
              ∷ mkMerge 5F 3F (seed 6)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 4F 3F (seed 2)
              ∷ mkMerge 3F 0F (seed 3)
              ∷ mkMerge 5F 1F (seed 4)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 4F 3F (seed 2)
              ∷ mkMerge 3F 0F (seed 3)
              ∷ mkMerge 5F 1F (seed 5)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 4F 3F (seed 2)
              ∷ mkMerge 3F 0F (seed 5)
              ∷ mkMerge 5F 0F (seed 7)
              ∷ [] )
            ∷ [] )
          ∷ ( ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 4F 3F (seed 2)
              ∷ mkMerge 5F 3F (seed 3)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 4F 3F (seed 2)
              ∷ mkMerge 5F 3F (seed 3)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 4F 3F (seed 2)
              ∷ mkMerge 5F 3F (seed 3)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 4F 3F (seed 2)
              ∷ mkMerge 5F 3F (seed 3)
              ∷ mkMerge 3F 0F (seed 4)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 4F 3F (seed 2)
              ∷ mkMerge 5F 3F (seed 3)
              ∷ mkMerge 3F 0F (seed 4)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 4F 3F (seed 2)
              ∷ mkMerge 5F 3F (seed 3)
              ∷ mkMerge 3F 0F (seed 6)
              ∷ [] )
            ∷ [] )
          ∷ ( ( mkMerge 3F 0F (seed 0)
              ∷ mkMerge 5F 1F (seed 1)
              ∷ [] )
            ∷ ( mkMerge 3F 0F (seed 0)
              ∷ mkMerge 5F 1F (seed 1)
              ∷ mkMerge 1F 0F (seed 2)
              ∷ mkMerge 2F 0F (seed 3)
              ∷ mkMerge 4F 3F (seed 4)
              ∷ [] )
            ∷ ( mkMerge 3F 0F (seed 0)
              ∷ mkMerge 5F 1F (seed 1)
              ∷ mkMerge 1F 0F (seed 2)
              ∷ mkMerge 2F 0F (seed 3)
              ∷ mkMerge 4F 3F (seed 4)
              ∷ [] )
            ∷ ( mkMerge 3F 0F (seed 0)
              ∷ mkMerge 5F 1F (seed 1)
              ∷ [] )
            ∷ ( mkMerge 3F 0F (seed 0)
              ∷ mkMerge 5F 1F (seed 1)
              ∷ mkMerge 4F 2F (seed 3)
              ∷ [] )
            ∷ ( mkMerge 3F 0F (seed 0)
              ∷ mkMerge 5F 1F (seed 1)
              ∷ mkMerge 1F 0F (seed 2)
              ∷ mkMerge 2F 0F (seed 3)
              ∷ mkMerge 4F 0F (seed 5)
              ∷ [] )
            ∷ [] )
          ∷ ( ( mkMerge 3F 0F (seed 0)
              ∷ mkMerge 4F 2F (seed 1)
              ∷ mkMerge 5F 1F (seed 2)
              ∷ [] )
            ∷ ( mkMerge 3F 0F (seed 0)
              ∷ mkMerge 4F 2F (seed 1)
              ∷ mkMerge 5F 1F (seed 2)
              ∷ mkMerge 1F 0F (seed 3)
              ∷ mkMerge 2F 0F (seed 4)
              ∷ [] )
            ∷ ( mkMerge 3F 0F (seed 0)
              ∷ mkMerge 4F 2F (seed 1)
              ∷ mkMerge 5F 1F (seed 2)
              ∷ mkMerge 1F 0F (seed 3)
              ∷ mkMerge 2F 0F (seed 4)
              ∷ [] )
            ∷ ( mkMerge 3F 0F (seed 0)
              ∷ mkMerge 4F 2F (seed 1)
              ∷ mkMerge 5F 1F (seed 2)
              ∷ [] )
            ∷ ( mkMerge 3F 0F (seed 0)
              ∷ mkMerge 4F 2F (seed 1)
              ∷ mkMerge 5F 1F (seed 2)
              ∷ [] )
            ∷ ( mkMerge 3F 0F (seed 0)
              ∷ mkMerge 4F 2F (seed 1)
              ∷ mkMerge 5F 1F (seed 2)
              ∷ mkMerge 1F 0F (seed 3)
              ∷ mkMerge 2F 0F (seed 4)
              ∷ [] )
            ∷ [] )
          ∷ ( ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 3F 0F (seed 2)
              ∷ mkMerge 4F 0F (seed 3)
              ∷ mkMerge 5F 0F (seed 4)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 3F 0F (seed 2)
              ∷ mkMerge 4F 0F (seed 3)
              ∷ mkMerge 5F 0F (seed 4)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 3F 0F (seed 2)
              ∷ mkMerge 4F 0F (seed 3)
              ∷ mkMerge 5F 0F (seed 4)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 3F 0F (seed 2)
              ∷ mkMerge 4F 0F (seed 3)
              ∷ mkMerge 5F 0F (seed 4)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 3F 0F (seed 2)
              ∷ mkMerge 4F 0F (seed 3)
              ∷ mkMerge 5F 0F (seed 4)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 3F 0F (seed 2)
              ∷ mkMerge 4F 0F (seed 3)
              ∷ mkMerge 5F 0F (seed 4)
              ∷ [] )
            ∷ [] )
          ∷ []
```

#### The verification

One decision for the whole certificate, one for the meet-table match; both
compute to `yes`{.AgdaInductiveConstructor} — that computation *is* the
re-verification of every engine claim above.

```agda
open LatticeCheck 𝑭 𝑺

certOK : LatticeCertOK cert
certOK = from-yes (latticeCertOK? cert)

certMeet : MeetMatches 𝑭 𝑺 𝑳 cert
certMeet = from-yes (meetMatches? 𝑭 𝑺 𝑳 cert)
```

#### The headline theorems

The target lattice is decidably representable, witnessed by this algebra;
and the certificate's congruence list is a complete Layer-D enumeration of
the algebra's decidable congruences.

```agda
HexagonEq6-Representableᵈ : Representableᵈ (toLattice 𝑳)
HexagonEq6-Representableᵈ = certRepresentableᵈ 𝑭 𝑺 𝑳 cert certOK certMeet

HexagonEq6-FiniteCongruencesᵈ : FiniteCongruencesᵈ 𝑨
HexagonEq6-FiniteCongruencesᵈ = certFiniteCongruencesᵈ cert certOK
```

--------------------------------------
