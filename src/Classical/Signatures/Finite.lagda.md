---
layout: default
file: "src/Classical/Signatures/Finite.lagda.md"
title: "Classical.Signatures.Finite module"
date: "2026-07-12"
author: "the agda-algebras development team"
---

### Finite finitary witnesses for concrete signatures

This is the [Classical.Signatures.Finite][] module of the [Agda Universal Algebra Library][].

The record `FiniteSignature`{.AgdaRecord} of [Setoid.Signatures.Finite][] packages
what it means for a signature to be *finite finitary*: a finite surjective
enumeration of its operation symbols, plus the `Finitary`{.AgdaFunction} witness
that every arity is finite.  This module supplies the two canonical sanity-check
instances, placed here — rather than beside the record — because concrete
signatures live in the `Classical/` tree and the `Setoid/` tree does not import it.

+  `Sig-Lattice`{.AgdaFunction} ([Classical.Signatures.Lattice][]): two binary
   operation symbols; both halves of the witness are finite case splits.
+  `Sig-Unary A`{.AgdaFunction} ([Classical.Signatures.Unary][]): one unary symbol
   per element of `A`; the witness is exactly an enumeration of `A`.

#### A caveat on enumerations up to `≈` versus up to `≡`

The symbol type of a signature is a *bare* type, so
`opEnum-sur`{.AgdaField} demands surjectivity up to propositional equality `_≡_`.
The carrier enumeration of a `FiniteAlgebra`{.AgdaRecord}
([Setoid.Algebras.Finite][]) is surjective only up to the carrier's setoid
equality `_≈_`, which is *not* enough here: on a quotient carrier the enumeration
hits every element up to the coarser `≈` while missing raw elements up to `≡`.
Consequently `Sig-Unary-FiniteSignature`{.AgdaFunction} below asks for an honest
`_≡_`-surjective enumeration of the bare type `A` rather than for a
`FiniteAlgebra`{.AgdaRecord} witness.  In the intended applications this costs
nothing: for a concrete finite group the raw carrier is typically `Fin n` or a
finite data type, where `≈` *is* `≡`; and the raw carrier of a quotient `G/H` is
that of `G` itself, so the same bare enumeration serves all coset algebras of `G`
with no choice of coset representatives.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Signatures.Finite where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive               using () renaming ( Set to Type )
open import Data.Fin.Base                using ( Fin ; zero ; suc )
open import Data.Nat.Base                using ( ℕ )
open import Data.Product                 using ( _,_ ; ∃-syntax )
open import Function.Construct.Identity  using ( ↔-id )
open import Level                        using ( Level )

open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Signatures.Lattice  using ( Sig-Lattice ; ∧-Op ; ∨-Op )
open import Classical.Signatures.Unary    using ( Sig-Unary )
open import Setoid.Congruences.ChainJoin  using ( Finitary )
open import Setoid.Signatures.Finite      using ( FiniteSignature )

open FiniteSignature
```
-->

#### The lattice signature is finite finitary

Both lattice operation symbols are binary, so the `Finitary`{.AgdaFunction}
witness names the identity bijection once per symbol, and the symbol enumeration
lists the two symbols.

```agda
-- Each lattice operation symbol has finite arity (namely 2).
finitary-Sig-Lattice : Finitary Sig-Lattice
finitary-Sig-Lattice ∧-Op = 2 , ↔-id _
finitary-Sig-Lattice ∨-Op = 2 , ↔-id _

-- The lattice signature is finite finitary.
Sig-Lattice-FiniteSignature : FiniteSignature Sig-Lattice
Sig-Lattice-FiniteSignature .opCard              = 2
Sig-Lattice-FiniteSignature .opEnum zero         = ∧-Op
Sig-Lattice-FiniteSignature .opEnum (suc zero)   = ∨-Op
Sig-Lattice-FiniteSignature .opEnum-sur ∧-Op     = zero , refl
Sig-Lattice-FiniteSignature .opEnum-sur ∨-Op     = suc zero , refl
Sig-Lattice-FiniteSignature .finitary            = finitary-Sig-Lattice
```

#### The unary signature over an enumerated symbol type

Given a surjective (up to `_≡_`; see the caveat above) enumeration of the bare
type `A`, the unary signature over `A` is finite finitary: the symbol enumeration
is the given one, and every arity is `Fin 1` definitionally.

```agda
module _ {ℓ : Level}{A : Type ℓ}
         (n : ℕ)(e : Fin n → A)(e-sur : (a : A) → ∃[ i ] e i ≡ a) where

  -- The unary signature over an enumerated symbol type is finite finitary.
  Sig-Unary-FiniteSignature : FiniteSignature (Sig-Unary A)
  Sig-Unary-FiniteSignature .opCard      = n
  Sig-Unary-FiniteSignature .opEnum      = e
  Sig-Unary-FiniteSignature .opEnum-sur  = e-sur
  Sig-Unary-FiniteSignature .finitary _  = 1 , ↔-id _
```

--------------------------------------
