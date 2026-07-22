---
layout: default
file: "src/Classical/Structures/Unary.lagda.md"
title: "Classical.Structures.Unary module"
date: "2026-07-22"
author: "the agda-algebras development team"
---

### Finite unary algebras from operation tables

This is the [Classical.Structures.Unary][] module of the [Agda Universal Algebra Library][].

A finite unary algebra — a carrier `Fin`{.AgdaDatatype}` n` with one unary
operation per symbol of `Fin`{.AgdaDatatype}` k` — is completely specified by a
`k × n` table of values, in exactly the way a binary operation is specified by
a Cayley table ([Overture.Cayley][]).  This module fixes that presentation and
its finiteness witnesses once, so that concrete unary algebras (G-sets given by
their action tables, and the certificate pipeline's externally computed
algebras — [Setoid.Congruences.Certificates][]) are literals plus one
constructor call, with no per-example boilerplate:

+  `tablesToUnaryAlgebra`{.AgdaFunction} — the algebra over
   `Sig-Unary (Fin k)` ([Classical.Signatures.Unary][]) whose
   `f`-th operation is row `f` of the table, built by
   `mkAlgebraₚ`{.AgdaFunction} over the propositional-equality carrier;
+  `tablesToUnaryAlgebra-FiniteAlgebra`{.AgdaFunction} — the carrier-finiteness
   witness ([Setoid.Algebras.Finite][]): decidable equality and the identity
   enumeration of `Fin`{.AgdaDatatype}` n`;
+  `Sig-Unary-Fin-FiniteSignature`{.AgdaFunction} — the signature-finiteness
   witness ([Setoid.Signatures.Finite][]): the identity enumeration of the
   symbol type `Fin`{.AgdaDatatype}` k`, through the general
   `Sig-Unary-FiniteSignature`{.AgdaFunction} of [Classical.Signatures.Finite][].

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Unary where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Data.Fin.Base                          using  ( Fin )
open import Data.Fin.Patterns                      using  ( 0F )
open import Data.Fin.Properties                    using  () renaming ( _≟_ to _≟ᶠ_ )
open import Data.Nat.Base                          using  ( ℕ )
open import Data.Product                           using  ( _,_ )
open import Data.Vec.Base                          using  ( Vec ; lookup )
open import Level                                  using  ( 0ℓ )
open import Relation.Binary.PropositionalEquality  using  ( refl ; cong )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Signatures.Finite  using  ( Sig-Unary-FiniteSignature )
open import Classical.Signatures.Unary   using  ( Sig-Unary )
open import Setoid.Algebras.Basic        using  ( Algebra ; mkAlgebraₚ )
open import Setoid.Algebras.Finite       using  ( FiniteAlgebra )
open import Setoid.Signatures.Finite     using  ( FiniteSignature )
```
-->

#### The algebra of a table

Row `f`, column `i` of the table is the value of the `f`-th operation at `i`.
The congruence obligation of `mkAlgebraₚ`{.AgdaFunction} is one
`cong`{.AgdaFunction} at the single argument position.

```agda
module _ (n k : ℕ) (tables : Vec (Vec (Fin n) n) k) where

  -- The f-th unary operation: row f of the table.
  unaryOp : Fin k → Fin n → Fin n
  unaryOp f i = lookup (lookup tables f) i

  -- The unary algebra presented by the table.
  tablesToUnaryAlgebra : Algebra {𝑆 = Sig-Unary (Fin k)} 0ℓ 0ℓ
  tablesToUnaryAlgebra =
    mkAlgebraₚ (Fin n)
               (λ f args → unaryOp f (args 0F))
               (λ f h → cong (unaryOp f) (h 0F))
```

#### The finiteness witnesses

The carrier is `Fin`{.AgdaDatatype}` n` on the nose, so decidable equality and a
surjective enumeration are the identity story; likewise for the symbol type
`Fin`{.AgdaDatatype}` k` on the signature side.

```agda
  -- The table algebra is a finite algebra.
  open FiniteAlgebra

  tablesToUnaryAlgebra-FiniteAlgebra : FiniteAlgebra tablesToUnaryAlgebra
  tablesToUnaryAlgebra-FiniteAlgebra ._≟_       = _≟ᶠ_
  tablesToUnaryAlgebra-FiniteAlgebra .card      = n
  tablesToUnaryAlgebra-FiniteAlgebra .enum      = λ i → i
  tablesToUnaryAlgebra-FiniteAlgebra .enum-sur  = λ x → x , refl

-- The unary signature on Fin k is finite finitary (identity enumeration).
Sig-Unary-Fin-FiniteSignature : (k : ℕ) → FiniteSignature (Sig-Unary (Fin k))
Sig-Unary-Fin-FiniteSignature k =
  Sig-Unary-FiniteSignature k (λ f → f) (λ f → f , refl)
```

--------------------------------------
