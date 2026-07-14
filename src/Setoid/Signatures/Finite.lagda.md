---
layout: default
file: "src/Setoid/Signatures/Finite.lagda.md"
title: "Setoid.Signatures.Finite module (The Agda Universal Algebra Library)"
date: "2026-07-12"
author: "the agda-algebras development team"
---

### Finite finitary signatures

This is the [Setoid.Signatures.Finite][] module of the [Agda Universal Algebra Library][].

A **finite finitary signature** has a finite type of operation symbols, each of
finite arity.  This module packages that notion as the record
`FiniteSignature`{.AgdaRecord} `𝑆`, the signature-side member of the library's
family of finiteness interfaces:

+  `FiniteSignature`{.AgdaRecord} (this module) — finiteness of the *signature*;
+  `FiniteAlgebra`{.AgdaRecord} ([Setoid.Algebras.Finite][]) — finiteness of the *carrier*;
+  `FiniteCongruences`{.AgdaRecord} ([Setoid.Congruences.Finite][]) — finite enumerability of the *congruence lattice*.

The three are logically independent and are kept as separate records so that each
consumer can demand exactly the finiteness it uses.  The first consumer of
`FiniteSignature`{.AgdaRecord} is the congruence-closure computation of
[Setoid.Congruences.Presented.Decidable][], which needs to search all operation
symbols and all arity-tuples of carrier indices; by contrast, the reconstruction
theorem of [Setoid.Congruences.Presented][] needs only carrier finiteness, which is
why signature finiteness is not a field of `FiniteAlgebra`{.AgdaRecord}.  This
packaging — a standalone record parameterized by the signature, rather than extra
fields on an algebra-level record — resolves audit A3 of the two-layer congruence
discipline (see `docs/adr/008-two-layer-congruence-discipline.md` and § 3–4 of
`docs/notes/flrp-two-layer-congruences.md`).

#### Why this module lives here

The notion is signature-level — no algebra and no setoid occurs in it — so the
natural candidates for its home are [Overture.Signatures][], where bare signatures
live, and this signature-generic corner of the `Setoid/` tree.  The deciding
constraint is the one-canonical-form rule: the library already has a canonical
statement that every arity of `𝑆` is finite, namely `Finitary`{.AgdaFunction} `𝑆`
of [Setoid.Congruences.ChainJoin][] (introduced there for the finitary Jónsson
theorem), and this record must reuse it rather than restate it.  An `Overture`
module cannot import from the `Setoid/` tree, so the record lands here, in
[Setoid.Signatures][]'s namespace — the `Setoid/` tree's home for signature-generic
material — as a module with no `{𝑆 : Signature 𝓞 𝓥}` parameter, for the same
reason as its parent: both the record and its fields take the signature as an
explicit argument and read no ambient signature.

#### Design of the operation-symbol half

Mirroring the carrier interface of [Setoid.Algebras.Finite][], the enumeration of
operation symbols is **surjective, not bijective**: a map `Fin opCard →`
`OperationSymbolsOf 𝑆` hitting every symbol is exactly what a proof needs in order
to *search* the symbols, and demanding injectivity would burden every instance with
distinctness proofs that no consumer uses, so `opCard`{.AgdaField} is an upper
bound on, not the exact size of, the symbol count.  Unlike the carrier case there
is no setoid in play: the symbol type is a bare type, so surjectivity is stated up
to propositional equality `_≡_`, and no decidable-equality field is included —
consumers iterate over the enumeration and never compare two symbols.

The arity half is the existing `Finitary`{.AgdaFunction} `𝑆`, i.e. a bijection
`ArityOf 𝑆 f ↔ Fin k` for each symbol `f`.  For the finitary signatures of
ordinary universal algebra this witness is a one-liner per symbol shape (see
[Examples.Setoid.FinitarySignatures][]); the derived accessors below repackage the
bijection as an enumeration `arEnum`{.AgdaFunction}, an index map
`arIdx`{.AgdaFunction}, and the round-trip law `arEnum-arIdx`{.AgdaFunction} that
downstream proofs use to pass between arity-tuples and vectors of indices.

Instances live downstream, where concrete signatures do:
`Classical.Signatures.Finite` provides witnesses for `Sig-Lattice`{.AgdaFunction}
and for the unary signature `Sig-Unary`{.AgdaFunction} `A`.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Signatures.Finite where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -----------------------------------
open import Data.Fin.Base     using ( Fin )
open import Data.Nat.Base     using ( ℕ )
open import Data.Product      using ( proj₁ ; proj₂ ; ∃-syntax )
open import Function.Bundles  using ( Inverse )
open import Level             using ( _⊔_ )

open import Relation.Binary.PropositionalEquality using ( _≡_ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture                      using  ( 𝓞 ; 𝓥 ; Signature
                                                 ; OperationSymbolsOf ; ArityOf )
open import Setoid.Congruences.ChainJoin  using  ( Finitary )
```
-->

#### The record

A **finite finitary signature** is a signature together with a finite surjective
enumeration of its operation symbols and, for each symbol, a bijection between its
arity type and a finite index type.

```agda
record FiniteSignature (𝑆 : Signature 𝓞 𝓥) : Type (𝓞 ⊔ 𝓥) where
  field
    opCard      : ℕ
    opEnum      : Fin opCard → OperationSymbolsOf 𝑆   -- finite symbol enumeration
    opEnum-sur  : (f : OperationSymbolsOf 𝑆) → ∃[ i ] opEnum i ≡ f
    finitary    : Finitary 𝑆                          -- each arity is finite
```

The derived accessors: `arCard f`{.AgdaFunction} is the arity of `f` as a natural
number, `arEnum f`{.AgdaFunction} enumerates the positions of `f`'s argument
tuples, `arIdx f`{.AgdaFunction} is the inverse index map, and
`arEnum-arIdx`{.AgdaFunction} is the round trip on the arity side, which is the
direction needed to reconstruct an arbitrary arity-tuple from its vector of
values on the enumeration.

```agda
  -- The (upper bound on the) number of argument positions of f.
  arCard : OperationSymbolsOf 𝑆 → ℕ
  arCard f = proj₁ (finitary f)

  -- The index of an argument position of f.
  arIdx : (f : OperationSymbolsOf 𝑆) → ArityOf 𝑆 f → Fin (arCard f)
  arIdx f = Inverse.to (proj₂ (finitary f))

  -- The argument position of f at a given index.
  arEnum : (f : OperationSymbolsOf 𝑆) → Fin (arCard f) → ArityOf 𝑆 f
  arEnum f = Inverse.from (proj₂ (finitary f))

  -- Round trip: recovering a position from its index is the identity.
  arEnum-arIdx : (f : OperationSymbolsOf 𝑆)(a : ArityOf 𝑆 f) → arEnum f (arIdx f a) ≡ a
  arEnum-arIdx f = Inverse.strictlyInverseʳ (proj₂ (finitary f))
```

--------------------------------------
