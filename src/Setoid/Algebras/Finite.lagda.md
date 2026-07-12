---
layout: default
file: "src/Setoid/Algebras/Finite.lagda.md"
title: "Setoid.Algebras.Finite module (The Agda Universal Algebra Library)"
date: "2026-07-12"
author: "the agda-algebras development team"
---

### Finite setoid algebras

This is the [Setoid.Algebras.Finite][] module of the [Agda Universal Algebra Library][].

This module defines the finiteness interface for setoid algebras.  The record
`FiniteAlgebra`{.AgdaRecord} `𝑨` bundles decidable setoid equality on the carrier of
`𝑨` with a finite, surjective enumeration of that carrier.  (It says nothing about
the congruences of `𝑨`; it is carrier-level data only.)

Two design points deserve comment.

+  **The enumeration is surjective, not bijective**.  A map `Fin card → 𝕌[ 𝑨 ]`
   hitting every element up to `≈` is exactly what downstream constructions need in
   order to *search* the carrier and to *count*; e.g., counting the pairs related by a
   congruence in [Setoid.Subalgebras.Subdirect.Finite][].  Demanding injectivity as
   well would burden every instance with distinctness proofs that no consumer uses,
   so `card`{.AgdaField} is an upper bound on, not the exact size of, the carrier.

+  **Decidable `≈` is a separate field**.  Surjective enumerability of a setoid
   carrier does not imply decidability of its equality, so the interface must ask
   for both.

The name `FiniteAlgebra`{.AgdaRecord} is deliberately reserved for this bare
interface.  Finite-algebra theorems about the *congruence lattice* — for instance
Birkhoff's subdirect representation theorem for finite algebras — need strictly more
than carrier finiteness: a complete, decidable enumeration of the congruences, which
carrier finiteness cannot supply constructively.  That stronger, logically
independent interface is `FiniteCongruences`{.AgdaRecord}, defined in
[Setoid.Congruences.Finite][]; the two are consumed together in
[Setoid.Subalgebras.Subdirect.Finite][].

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Algebras.Finite {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -----------------------------------
open import Data.Fin.Base     using ( Fin ; zero )
open import Data.Nat.Base     using ( ℕ )
open import Data.Product      using ( _,_  ; ∃-syntax )
open import Data.Unit.Base    using ( ⊤ ; tt )
open import Function          using ( Func )
open import Level             using ( Level ; _⊔_ ; 0ℓ )
open import Relation.Binary   using ( Setoid )
open import Relation.Nullary  using ( Dec ; yes )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Setoid.Algebras.Basic {𝑆 = 𝑆} using ( Algebra ; 𝕌[_] ; 𝔻[_] )

open Algebra  using ( Domain ; Interp )
open Func     using ( cong ) renaming ( to to _⟨$⟩_ )
open Relation.Binary.IsEquivalence


private variable α ρ : Level
```
-->

#### The bare finiteness interface

A **finite algebra** is an algebra together with a decision procedure for its setoid
equality and a surjective enumeration of its carrier by a finite index type.

```agda
record FiniteAlgebra (𝑨 : Algebra α ρ) : Type (α ⊔ ρ) where
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ )
  field
    _≟_       : ∀ x y → Dec (x ≈ y)      -- decidable setoid equality carrier of 𝑨
    card      : ℕ
    enum      : Fin card → 𝕌[ 𝑨 ]       -- finite enumeration of the carrier
    enum-sur  : ∀ x → ∃[ i ] enum i ≈ x  -- that hits every element, up to ≈
open FiniteAlgebra
```

#### Non-vacuity: the one-element algebra is finite

The record is genuine, computational data, so we exhibit an inhabitant.  The
one-element algebra `𝟏`{.AgdaFunction} over the ambient signature has carrier `⊤`,
trivial setoid equality, and each operation constantly `tt`; its finiteness witness
is immediate.[^1]

```agda
-- The one-element algebra over the signature 𝑆.
open Setoid

𝟏 : Algebra 0ℓ 0ℓ
𝟏 .Domain .Carrier        = ⊤
𝟏 .Domain ._≈_            = λ _ _ → ⊤
𝟏 .Domain .isEquivalence  = record  { refl   = tt
                                    ; sym    = λ _ → tt
                                    ; trans  = λ _ _ → tt }
𝟏 .Interp ⟨$⟩ _           = tt
𝟏 .Interp .cong _         = tt

-- The one-element algebra is a finite algebra.
𝟏-FiniteAlgebra : FiniteAlgebra 𝟏
𝟏-FiniteAlgebra ._≟_       = λ _ _ → yes tt
𝟏-FiniteAlgebra .card      = 1
𝟏-FiniteAlgebra .enum      = λ _ → tt
𝟏-FiniteAlgebra .enum-sur  = λ _ → zero , tt
```

--------------------------------------

[^1]:  The finiteness witness of the congruence lattice of 𝟏 is
       `𝟏-FiniteCongruences`{.AgdaFunction} in [Setoid.Congruences.Finite][] which,
       together with the witness `𝟏-FiniteAlgebra`{.AgdaFunction}, is consumed by
       Birkhoff's theorem for finite algebras in [Setoid.Subalgebras.Subdirect.Finite][].
