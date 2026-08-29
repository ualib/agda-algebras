---
layout: default
file: "src/Setoid/Algebras/Finite/Irredundant.lagda.md"
title: "Setoid.Algebras.Finite.Irredundant module (The Agda Universal Algebra Library)"
date: "2026-07-28"
author: "the agda-algebras development team"
---

### Irredundant enumerations of a finite carrier

This is the [Setoid.Algebras.Finite.Irredundant][] module of the [Agda Universal Algebra Library][].

The finiteness interface `FiniteAlgebra`{.AgdaRecord} of [Setoid.Algebras.Finite][]
deliberately asks for a *surjective* enumeration only: `card`{.AgdaField} is an
upper bound on the size of the carrier, and the same element may be hit many
times.  That is the right interface for searching, but some constructions need
the enumeration to be a *bijection up to `≈`* — one index per `≈`-class — so that
the index set `Fin`{.AgdaDatatype}` m` is a faithful copy of the carrier.

The first consumer is the Kurzweil–Netter duality proof ([FLRP.KurzweilNetter][],
issue #502), which represents the dual of `Con 𝑨` on a power `S^m` *indexed by the
carrier* of `𝑨`{.AgdaBound}: there the partitions of the index set must correspond
exactly to the decidable equivalences on the carrier, which forces the enumeration
to identify no two indices (a redundant index would admit partitions separating
two copies of one element, and the correspondence would break).

This module upgrades any `FiniteAlgebra`{.AgdaRecord} witness to an
**irredundant enumeration**: a size `icard`{.AgdaField}, an enumeration
`ienum`{.AgdaField} that is still surjective up to `≈`, and an injectivity
proof `ienum-inj`{.AgdaField} stating that `≈`-equal values have equal indices.
The construction is elementary and fully constructive: list the enumerated
values, `deduplicate`{.AgdaFunction} the list using the decidable equality
carried by the finiteness witness, and read the deduplicated list back as a
function on its positions.  Surjectivity survives deduplication by the standard
library's membership lemmas, and injectivity is exactly the pairwise
distinctness (`Unique`{.AgdaFunction}) of the deduplicated list.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Algebras.Finite.Irredundant where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty          using ( ⊥-elim )
open import Data.Fin.Base       using ( Fin ; zero ; suc ) renaming ( _<_ to _<ᶠ_ )
open import Data.Fin.Properties using ( <-cmp )
open import Data.List.Base      using ( List ; length ; lookup ; tabulate
                                      ; deduplicate )
open import Data.Nat.Base       using ( ℕ ; s≤s )
open import Data.Product        using ( _,_ ; proj₁ ; proj₂ ; ∃-syntax )
open import Level               using ( Level ; _⊔_ )
open import Relation.Binary     using ( Setoid ; DecSetoid )
open import Relation.Binary.Definitions           using ( tri< ; tri≈ ; tri> )
open import Relation.Binary.PropositionalEquality using ( _≡_ )
open import Relation.Nullary    using ( ¬_ )

open import Data.List.Relation.Unary.All       using ( All ; [] ; _∷_ )
open import Data.List.Relation.Unary.AllPairs  using ( AllPairs ; [] ; _∷_ )
open import Data.List.Relation.Unary.Any       using ( Any ; index )
open import Data.List.Relation.Unary.Any.Properties  using ( lookup-index )

import Data.List.Membership.Setoid.Properties             as MembershipP
import Data.List.Relation.Unary.Unique.DecSetoid.Properties as UniqueP

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Overture               using ( 𝓞 ; 𝓥 ; Signature )
open import Setoid.Algebras.Basic  using ( Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Algebras.Finite using ( FiniteAlgebra )

private variable α ρ ℓ : Level
```
-->

#### The interface

An **irredundant enumeration** of the carrier of `𝑨`{.AgdaBound} is a surjective
enumeration that hits each `≈`-class exactly once: `≈`-equal values have
propositionally equal indices.  (Injectivity is stated in this converse-kernel
form because it is the form consumers use: it makes the index map
`x ↦ proj₁ (ienum-sur x)` a well-defined function on `≈`-classes.)

```agda
module _ {𝑆 : Signature 𝓞 𝓥} (𝑨 : Algebra {𝑆 = 𝑆} α ρ) where

  open Setoid 𝔻[ 𝑨 ] using ( _≈_ )

  record IrredundantEnumeration : Type (α ⊔ ρ) where
    field
      icard      : ℕ
      ienum      : Fin icard → 𝕌[ 𝑨 ]
      ienum-sur  : ∀ x → ∃[ i ] ienum i ≈ x                 -- still hits everything
      ienum-inj  : ∀ {i j} → ienum i ≈ ienum j → i ≡ j      -- but nothing twice
```

#### Two private list lemmas

Positions of a list of pairwise-distinct elements carry the distinctness: the
values at two positions in `<`-order are related by the pairwise relation.  (The
standard library states `AllPairs`{.AgdaDatatype} by structural induction; these
two small lemmas read it back through positional `lookup`{.AgdaFunction}.)

```agda
module _ {A : Type α} where

  private
    -- The value at each position of an All-covered list satisfies the predicate.
    lookup-All : {P : A → Type ℓ} {xs : List A}
      → All P xs → (i : Fin (length xs)) → P (lookup xs i)
    lookup-All []         ()
    lookup-All (px ∷ pxs) zero     = px
    lookup-All (px ∷ pxs) (suc i)  = lookup-All pxs i

  -- Values at <-ordered positions of an AllPairs-covered list are related.
  lookup-AllPairs : {R : A → A → Type ℓ} {xs : List A} → AllPairs R xs
    → {i j : Fin (length xs)} → i <ᶠ j → R (lookup xs i) (lookup xs j)
  lookup-AllPairs []         {i = ()}
  lookup-AllPairs (px ∷ pxs) {i}      {zero}  ()
  lookup-AllPairs (px ∷ pxs) {zero}   {suc j} _          = lookup-All px j
  lookup-AllPairs (px ∷ pxs) {suc i}  {suc j} (s≤s i<j)  =
    lookup-AllPairs pxs {i} {j} i<j
```

#### The construction

Deduplicating the value list of the given enumeration yields the irredundant one.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} (𝑭 : FiniteAlgebra 𝑨) where

  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; sym ; trans )
  open FiniteAlgebra 𝑭 using ( _≟_ ; enum ; enum-sur )

  private
    -- The carrier's decidable-setoid bundle, for the deduplication lemmas.
    DS : DecSetoid α ρ
    DS = record
      { Carrier           = 𝕌[ 𝑨 ]
      ; _≈_               = _≈_
      ; isDecEquivalence  = record
          { isEquivalence  = Setoid.isEquivalence 𝔻[ 𝑨 ]
          ; _≟_            = _≟_
          }
      }

    -- The enumerated values, as a list, deduplicated up to ≈.
    values : List 𝕌[ 𝑨 ]
    values = tabulate enum

    dedup : List 𝕌[ 𝑨 ]
    dedup = deduplicate _≟_ values

    -- Membership in the value list survives deduplication (≈ respects itself).
    ∈-dedup : {x : 𝕌[ 𝑨 ]} → Any (x ≈_) values → Any (x ≈_) dedup
    ∈-dedup = MembershipP.∈-deduplicate⁺ 𝔻[ 𝑨 ] _≟_ (λ b≈a x≈a → trans x≈a (sym b≈a))

    -- The deduplicated list is pairwise ≈-distinct.
    dedup-distinct : AllPairs (λ x y → ¬ (x ≈ y)) dedup
    dedup-distinct = UniqueP.deduplicate-! DS values
```

The three fields.  Surjectivity chases an element through its original
enumeration index and the membership lemmas; injectivity turns an `≈`-collision
of two distinct positions into a contradiction with pairwise distinctness, by
trichotomy on the positions.

```agda
  irredundantEnumeration : IrredundantEnumeration 𝑨
  irredundantEnumeration = record
    { icard      = length dedup
    ; ienum      = lookup dedup
    ; ienum-sur  = sur
    ; ienum-inj  = λ {i} {j} → inj {i} {j}
    }
    where
    sur : ∀ x → ∃[ i ] lookup dedup i ≈ x
    sur x = index mem , trans (sym (lookup-index mem)) (proj₂ (enum-sur x))
      where
      -- enum i₀ is in the value list, hence in the deduplicated list.
      mem : Any (enum (proj₁ (enum-sur x)) ≈_) dedup
      mem = ∈-dedup (MembershipP.∈-tabulate⁺ 𝔻[ 𝑨 ] (proj₁ (enum-sur x)))

    inj : ∀ {i j} → lookup dedup i ≈ lookup dedup j → i ≡ j
    inj {i} {j} e with <-cmp i j
    ... | tri<  i<j _ _  = ⊥-elim (lookup-AllPairs dedup-distinct i<j e)
    ... | tri≈  _ i≡j _  = i≡j
    ... | tri>  _ _ j<i  = ⊥-elim (lookup-AllPairs dedup-distinct j<i (sym e))
```

--------------------------------------
