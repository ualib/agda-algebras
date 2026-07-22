---
layout: default
file: "src/FLRP/Certificates/SmallLatticeReps/SLR30.lagda.md"
title: "FLRP.Certificates.SmallLatticeReps.SLR30 module (The Agda Universal Algebra Library)"
date: "2026-07-22"
author: "the agda-algebras development team (emitted by scripts/python/flrp)"
---

### A machine-checked representation: Con(B30) ≅ manuscript L30

This is the [FLRP.Certificates.SmallLatticeReps.SLR30][] module of the [Agda Universal Algebra Library][].

**This module was emitted by `scripts/python/flrp/emit_agda.py` from
`scripts/python/flrp/inputs/slr/slr30.json`.  Do not edit it by hand; rerun the emitter instead.**

`B30`/`L30` in the numbering of the DeMeo–Freese–Jipsen manuscript *Representing Finite Lattices as Congruence Lattices of Finite Algebras* (§ 6 of the 2016-06-10 draft, `docs/papers/fin-lat-rep/SmallLatticeReps.tex`).  The dictionary between the manuscript's lattice numbering and this library's names is `docs/notes/flrp-slr-naming.md`.

It re-verifies, end-to-end through the WP-6 certificate pipeline (#457), the
claim that the congruence lattice of the algebra "B30" — carrier size
5, unary operations `f`, `g` — is isomorphic to the lattice
"manuscript L30" (7 elements).  The engine's output below (normal-form
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

module FLRP.Certificates.SmallLatticeReps.SLR30 where

-- Imports from Agda and the Agda Standard Library -----------------------------
open import Data.Fin.Base       using ( Fin )
open import Data.Fin.Patterns   using ( 0F ; 1F ; 2F ; 3F ; 4F ; 5F ; 6F )
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
opTables : Vec (Vec (Fin 5) 5) 2
opTables = (0F ∷ 3F ∷ 4F ∷ 3F ∷ 4F ∷ [])
         ∷ (2F ∷ 2F ∷ 1F ∷ 4F ∷ 3F ∷ [])
         ∷ []

𝑨 : Algebra {𝑆 = Sig-Unary (Fin 2)} 0ℓ 0ℓ
𝑨 = tablesToUnaryAlgebra 5 2 opTables

𝑭 : FiniteAlgebra 𝑨
𝑭 = tablesToUnaryAlgebra-FiniteAlgebra 5 2 opTables

𝑺 : FiniteSignature (Sig-Unary (Fin 2))
𝑺 = Sig-Unary-Fin-FiniteSignature 2
```

#### The target lattice, from its Cayley tables

The claimed congruence lattice "manuscript L30", presented exactly as the
worked lattice examples are ([Examples.Classical.Lattices.L7][]): meet and
join tables, every law discharged by decision over the finite carrier.

```agda
∧-table ∨-table : Table 7
∧-table = (0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ [])
        ∷ (0F ∷ 1F ∷ 0F ∷ 1F ∷ 0F ∷ 1F ∷ 1F ∷ [])
        ∷ (0F ∷ 0F ∷ 2F ∷ 0F ∷ 2F ∷ 2F ∷ 2F ∷ [])
        ∷ (0F ∷ 1F ∷ 0F ∷ 3F ∷ 0F ∷ 3F ∷ 3F ∷ [])
        ∷ (0F ∷ 0F ∷ 2F ∷ 0F ∷ 4F ∷ 2F ∷ 4F ∷ [])
        ∷ (0F ∷ 1F ∷ 2F ∷ 3F ∷ 2F ∷ 5F ∷ 5F ∷ [])
        ∷ (0F ∷ 1F ∷ 2F ∷ 3F ∷ 4F ∷ 5F ∷ 6F ∷ [])
        ∷ []

∨-table = (0F ∷ 1F ∷ 2F ∷ 3F ∷ 4F ∷ 5F ∷ 6F ∷ [])
        ∷ (1F ∷ 1F ∷ 5F ∷ 3F ∷ 6F ∷ 5F ∷ 6F ∷ [])
        ∷ (2F ∷ 5F ∷ 2F ∷ 5F ∷ 4F ∷ 5F ∷ 6F ∷ [])
        ∷ (3F ∷ 3F ∷ 5F ∷ 3F ∷ 6F ∷ 5F ∷ 6F ∷ [])
        ∷ (4F ∷ 6F ∷ 4F ∷ 6F ∷ 4F ∷ 6F ∷ 6F ∷ [])
        ∷ (5F ∷ 5F ∷ 5F ∷ 5F ∷ 6F ∷ 5F ∷ 6F ∷ [])
        ∷ (6F ∷ 6F ∷ 6F ∷ 6F ∷ 6F ∷ 6F ∷ 6F ∷ [])
        ∷ []

open FiniteLattice

𝑳 : FiniteLattice
𝑳 .size     = 6
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

cert : LatticeCert 5 2 arOf 7
cert = mkLatticeCert partsᵛ 0F prinᵛ prinTrᵛ ∧-table ∨-table joinTrᵛ
  where
  partsᵛ : Vec (ParentVec 5) 7
  partsᵛ = (0F ∷ 1F ∷ 2F ∷ 3F ∷ 4F ∷ [])
         ∷ (0F ∷ 1F ∷ 2F ∷ 3F ∷ 3F ∷ [])
         ∷ (0F ∷ 1F ∷ 2F ∷ 1F ∷ 2F ∷ [])
         ∷ (0F ∷ 1F ∷ 1F ∷ 3F ∷ 3F ∷ [])
         ∷ (0F ∷ 0F ∷ 2F ∷ 0F ∷ 2F ∷ [])
         ∷ (0F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ [])
         ∷ (0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ [])
         ∷ []

  prinᵛ : Vec (Vec (Fin 7) 5) 5
  prinᵛ = (0F ∷ 4F ∷ 6F ∷ 4F ∷ 6F ∷ [])
        ∷ (4F ∷ 0F ∷ 3F ∷ 2F ∷ 5F ∷ [])
        ∷ (6F ∷ 3F ∷ 0F ∷ 5F ∷ 2F ∷ [])
        ∷ (4F ∷ 2F ∷ 5F ∷ 0F ∷ 1F ∷ [])
        ∷ (6F ∷ 5F ∷ 2F ∷ 1F ∷ 0F ∷ [])
        ∷ []

  prinTrᵛ : Vec (Vec (Trace 5 2 arOf) 5) 5
  prinTrᵛ = ( []
            ∷ ( mkMerge 0F 1F (seed 0)
              ∷ mkMerge 0F 3F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 2F 4F (translate 1F 0F (0F ∷ []) 0)
              ∷ [] )
            ∷ ( mkMerge 0F 2F (seed 0)
              ∷ mkMerge 0F 4F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 2F 1F (translate 1F 0F (0F ∷ []) 1)
              ∷ mkMerge 2F 3F (translate 1F 0F (0F ∷ []) 1)
              ∷ [] )
            ∷ ( mkMerge 0F 3F (seed 0)
              ∷ mkMerge 2F 4F (translate 1F 0F (0F ∷ []) 0)
              ∷ mkMerge 1F 3F (translate 1F 0F (0F ∷ []) 0)
              ∷ [] )
            ∷ ( mkMerge 0F 4F (seed 0)
              ∷ mkMerge 2F 3F (translate 1F 0F (0F ∷ []) 0)
              ∷ mkMerge 4F 3F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 1F 4F (translate 1F 0F (0F ∷ []) 1)
              ∷ [] )
            ∷ [] )
          ∷ ( ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 3F 0F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 4F 2F (translate 1F 0F (0F ∷ []) 0)
              ∷ [] )
            ∷ []
            ∷ ( mkMerge 1F 2F (seed 0)
              ∷ mkMerge 3F 4F (translate 0F 0F (0F ∷ []) 0)
              ∷ [] )
            ∷ ( mkMerge 1F 3F (seed 0)
              ∷ mkMerge 2F 4F (translate 1F 0F (0F ∷ []) 0)
              ∷ [] )
            ∷ ( mkMerge 1F 4F (seed 0)
              ∷ mkMerge 3F 4F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 2F 3F (translate 1F 0F (0F ∷ []) 1)
              ∷ [] )
            ∷ [] )
          ∷ ( ( mkMerge 2F 0F (seed 0)
              ∷ mkMerge 4F 0F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 1F 2F (translate 1F 0F (0F ∷ []) 1)
              ∷ mkMerge 3F 2F (translate 1F 0F (0F ∷ []) 1)
              ∷ [] )
            ∷ ( mkMerge 2F 1F (seed 0)
              ∷ mkMerge 4F 3F (translate 0F 0F (0F ∷ []) 0)
              ∷ [] )
            ∷ []
            ∷ ( mkMerge 2F 3F (seed 0)
              ∷ mkMerge 4F 3F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 1F 4F (translate 1F 0F (0F ∷ []) 1)
              ∷ [] )
            ∷ ( mkMerge 2F 4F (seed 0)
              ∷ mkMerge 1F 3F (translate 1F 0F (0F ∷ []) 0)
              ∷ [] )
            ∷ [] )
          ∷ ( ( mkMerge 3F 0F (seed 0)
              ∷ mkMerge 4F 2F (translate 1F 0F (0F ∷ []) 0)
              ∷ mkMerge 3F 1F (translate 1F 0F (0F ∷ []) 0)
              ∷ [] )
            ∷ ( mkMerge 3F 1F (seed 0)
              ∷ mkMerge 4F 2F (translate 1F 0F (0F ∷ []) 0)
              ∷ [] )
            ∷ ( mkMerge 3F 2F (seed 0)
              ∷ mkMerge 3F 4F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 4F 1F (translate 1F 0F (0F ∷ []) 1)
              ∷ [] )
            ∷ []
            ∷ (mkMerge 3F 4F (seed 0) ∷ [])
            ∷ [] )
          ∷ ( ( mkMerge 4F 0F (seed 0)
              ∷ mkMerge 3F 2F (translate 1F 0F (0F ∷ []) 0)
              ∷ mkMerge 3F 4F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 4F 1F (translate 1F 0F (0F ∷ []) 1)
              ∷ [] )
            ∷ ( mkMerge 4F 1F (seed 0)
              ∷ mkMerge 4F 3F (translate 0F 0F (0F ∷ []) 0)
              ∷ mkMerge 3F 2F (translate 1F 0F (0F ∷ []) 1)
              ∷ [] )
            ∷ ( mkMerge 4F 2F (seed 0)
              ∷ mkMerge 3F 1F (translate 1F 0F (0F ∷ []) 0)
              ∷ [] )
            ∷ (mkMerge 4F 3F (seed 0) ∷ [])
            ∷ []
            ∷ [] )
          ∷ []

  joinTrᵛ : Vec (Vec (Trace 5 2 arOf) 7) 7
  joinTrᵛ = ( []
            ∷ (mkMerge 4F 3F (seed 0) ∷ [])
            ∷ ( mkMerge 3F 1F (seed 0)
              ∷ mkMerge 4F 2F (seed 1)
              ∷ [] )
            ∷ ( mkMerge 2F 1F (seed 0)
              ∷ mkMerge 4F 3F (seed 1)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 3F 0F (seed 1)
              ∷ mkMerge 4F 2F (seed 2)
              ∷ [] )
            ∷ ( mkMerge 2F 1F (seed 0)
              ∷ mkMerge 3F 1F (seed 1)
              ∷ mkMerge 4F 1F (seed 2)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 3F 0F (seed 2)
              ∷ mkMerge 4F 0F (seed 3)
              ∷ [] )
            ∷ [] )
          ∷ ( (mkMerge 4F 3F (seed 0) ∷ [])
            ∷ (mkMerge 4F 3F (seed 0) ∷ [])
            ∷ ( mkMerge 4F 3F (seed 0)
              ∷ mkMerge 3F 1F (seed 1)
              ∷ mkMerge 4F 2F (seed 2)
              ∷ [] )
            ∷ ( mkMerge 4F 3F (seed 0)
              ∷ mkMerge 2F 1F (seed 1)
              ∷ [] )
            ∷ ( mkMerge 4F 3F (seed 0)
              ∷ mkMerge 1F 0F (seed 1)
              ∷ mkMerge 3F 0F (seed 2)
              ∷ mkMerge 4F 2F (seed 3)
              ∷ [] )
            ∷ ( mkMerge 4F 3F (seed 0)
              ∷ mkMerge 2F 1F (seed 1)
              ∷ mkMerge 3F 1F (seed 2)
              ∷ [] )
            ∷ ( mkMerge 4F 3F (seed 0)
              ∷ mkMerge 1F 0F (seed 1)
              ∷ mkMerge 2F 0F (seed 2)
              ∷ mkMerge 3F 0F (seed 3)
              ∷ [] )
            ∷ [] )
          ∷ ( ( mkMerge 3F 1F (seed 0)
              ∷ mkMerge 4F 2F (seed 1)
              ∷ [] )
            ∷ ( mkMerge 3F 1F (seed 0)
              ∷ mkMerge 4F 2F (seed 1)
              ∷ mkMerge 4F 3F (seed 2)
              ∷ [] )
            ∷ ( mkMerge 3F 1F (seed 0)
              ∷ mkMerge 4F 2F (seed 1)
              ∷ [] )
            ∷ ( mkMerge 3F 1F (seed 0)
              ∷ mkMerge 4F 2F (seed 1)
              ∷ mkMerge 2F 1F (seed 2)
              ∷ [] )
            ∷ ( mkMerge 3F 1F (seed 0)
              ∷ mkMerge 4F 2F (seed 1)
              ∷ mkMerge 1F 0F (seed 2)
              ∷ [] )
            ∷ ( mkMerge 3F 1F (seed 0)
              ∷ mkMerge 4F 2F (seed 1)
              ∷ mkMerge 2F 1F (seed 2)
              ∷ [] )
            ∷ ( mkMerge 3F 1F (seed 0)
              ∷ mkMerge 4F 2F (seed 1)
              ∷ mkMerge 1F 0F (seed 2)
              ∷ mkMerge 2F 0F (seed 3)
              ∷ [] )
            ∷ [] )
          ∷ ( ( mkMerge 2F 1F (seed 0)
              ∷ mkMerge 4F 3F (seed 1)
              ∷ [] )
            ∷ ( mkMerge 2F 1F (seed 0)
              ∷ mkMerge 4F 3F (seed 1)
              ∷ [] )
            ∷ ( mkMerge 2F 1F (seed 0)
              ∷ mkMerge 4F 3F (seed 1)
              ∷ mkMerge 3F 1F (seed 2)
              ∷ [] )
            ∷ ( mkMerge 2F 1F (seed 0)
              ∷ mkMerge 4F 3F (seed 1)
              ∷ [] )
            ∷ ( mkMerge 2F 1F (seed 0)
              ∷ mkMerge 4F 3F (seed 1)
              ∷ mkMerge 1F 0F (seed 2)
              ∷ mkMerge 3F 0F (seed 3)
              ∷ [] )
            ∷ ( mkMerge 2F 1F (seed 0)
              ∷ mkMerge 4F 3F (seed 1)
              ∷ mkMerge 3F 1F (seed 3)
              ∷ [] )
            ∷ ( mkMerge 2F 1F (seed 0)
              ∷ mkMerge 4F 3F (seed 1)
              ∷ mkMerge 1F 0F (seed 2)
              ∷ mkMerge 3F 0F (seed 4)
              ∷ [] )
            ∷ [] )
          ∷ ( ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 3F 0F (seed 1)
              ∷ mkMerge 4F 2F (seed 2)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 3F 0F (seed 1)
              ∷ mkMerge 4F 2F (seed 2)
              ∷ mkMerge 4F 3F (seed 3)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 3F 0F (seed 1)
              ∷ mkMerge 4F 2F (seed 2)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 3F 0F (seed 1)
              ∷ mkMerge 4F 2F (seed 2)
              ∷ mkMerge 2F 1F (seed 3)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 3F 0F (seed 1)
              ∷ mkMerge 4F 2F (seed 2)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 3F 0F (seed 1)
              ∷ mkMerge 4F 2F (seed 2)
              ∷ mkMerge 2F 1F (seed 3)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 3F 0F (seed 1)
              ∷ mkMerge 4F 2F (seed 2)
              ∷ mkMerge 2F 0F (seed 4)
              ∷ [] )
            ∷ [] )
          ∷ ( ( mkMerge 2F 1F (seed 0)
              ∷ mkMerge 3F 1F (seed 1)
              ∷ mkMerge 4F 1F (seed 2)
              ∷ [] )
            ∷ ( mkMerge 2F 1F (seed 0)
              ∷ mkMerge 3F 1F (seed 1)
              ∷ mkMerge 4F 1F (seed 2)
              ∷ [] )
            ∷ ( mkMerge 2F 1F (seed 0)
              ∷ mkMerge 3F 1F (seed 1)
              ∷ mkMerge 4F 1F (seed 2)
              ∷ [] )
            ∷ ( mkMerge 2F 1F (seed 0)
              ∷ mkMerge 3F 1F (seed 1)
              ∷ mkMerge 4F 1F (seed 2)
              ∷ [] )
            ∷ ( mkMerge 2F 1F (seed 0)
              ∷ mkMerge 3F 1F (seed 1)
              ∷ mkMerge 4F 1F (seed 2)
              ∷ mkMerge 1F 0F (seed 3)
              ∷ [] )
            ∷ ( mkMerge 2F 1F (seed 0)
              ∷ mkMerge 3F 1F (seed 1)
              ∷ mkMerge 4F 1F (seed 2)
              ∷ [] )
            ∷ ( mkMerge 2F 1F (seed 0)
              ∷ mkMerge 3F 1F (seed 1)
              ∷ mkMerge 4F 1F (seed 2)
              ∷ mkMerge 1F 0F (seed 3)
              ∷ [] )
            ∷ [] )
          ∷ ( ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 3F 0F (seed 2)
              ∷ mkMerge 4F 0F (seed 3)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 3F 0F (seed 2)
              ∷ mkMerge 4F 0F (seed 3)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 3F 0F (seed 2)
              ∷ mkMerge 4F 0F (seed 3)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 3F 0F (seed 2)
              ∷ mkMerge 4F 0F (seed 3)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 3F 0F (seed 2)
              ∷ mkMerge 4F 0F (seed 3)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 3F 0F (seed 2)
              ∷ mkMerge 4F 0F (seed 3)
              ∷ [] )
            ∷ ( mkMerge 1F 0F (seed 0)
              ∷ mkMerge 2F 0F (seed 1)
              ∷ mkMerge 3F 0F (seed 2)
              ∷ mkMerge 4F 0F (seed 3)
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
SLR30-Representableᵈ : Representableᵈ (toLattice 𝑳)
SLR30-Representableᵈ = certRepresentableᵈ 𝑭 𝑺 𝑳 cert certOK certMeet

SLR30-FiniteCongruencesᵈ : FiniteCongruencesᵈ 𝑨
SLR30-FiniteCongruencesᵈ = certFiniteCongruencesᵈ cert certOK
```

--------------------------------------
