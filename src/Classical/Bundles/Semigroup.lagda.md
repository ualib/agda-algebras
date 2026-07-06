---
layout: default
file: "src/Classical/Bundles/Semigroup.lagda.md"
title: "Classical.Bundles.Semigroup module"
date: "2026-05-18"
author: "the agda-algebras development team"
---

### Bundle bridge for semigroups

This is the [Classical.Bundles.Semigroup][] module of the [Agda Universal Algebra Library][].

This module supplies the bidirectional bridge between the Σ-typed core of
[`Classical.Structures.Semigroup`][] and the record-typed `Algebra.Bundles.Semigroup`
in the Agda standard library.  Both representations carry the same mathematical
content; the bridge exists so that downstream code typed against
`Algebra.Bundles.Semigroup` is reusable against the canonical agda-algebras
representation without manual record-shuffling.

The round-trip is stated *pointwise* on the carrier, in the semigroup's underlying
setoid equivalence, per
[ADR-002 v2 §6](../../docs/adr/002-classical-layer-design.md).  The same
Fin 2 η-failure under `--cubical-compatible` that motivated the pointwise
round-trip for Magma applies here unchanged — the equation-witness layer adds
nothing new to the bridge's obstruction analysis, only to its content, and that
content (the curried associativity law) is supplied ready-made by
`Semigroup-Op.assoc-law`, so the bridge itself stays a thin record-shuffle.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Bundles.Semigroup where

-- Imports from the Agda Standard Library -----------------------------------------
open import Algebra.Bundles     using () renaming ( Semigroup to stdlib-Semigroup )
open import Data.Fin.Patterns   using ( 0F ; 1F ; 2F )
open import Data.Product        using ( _,_ )
open import Function            using ( Func )
open import Level               using ( Level )
open import Relation.Binary     using ( Setoid )
import Relation.Binary.PropositionalEquality as ≡
open Func renaming ( to to _⟨$⟩_ )

-- Imports from the Agda Universal Algebra Library --------------------------------
open import Classical.Signatures.Magma             using  ( ∙-Op ; Sig-Magma )
open import Classical.Structures.Semigroup         using  ( Semigroup ; semigroup→magma
                                                          ; module Semigroup-Op )
open import Classical.Theories.Semigroup           using  ( assoc )

open import Setoid.Algebras.Basic {𝑆 = Sig-Magma}  using  ( Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Signatures                      using  ( ⟨_⟩ )

private variable α ρ : Level
```
-->

#### Core to stdlib bundle

Going from the canonical Σ-typed core to the stdlib record reads off the domain's
`Carrier` and `_≈_` and exposes the operation and both law-fields through
`open Semigroup-Op 𝑺`.  The `isMagma.∙-cong` and `isSemigroup.assoc` fields are
*exactly* `Semigroup-Op`'s `∙-cong` and `assoc-law` — both already in curried form —
so this direction is pure field-plumbing with no proof content of its own.  All of
the Fin 2 η-bridging between term-interpretation form and curried form is discharged
once, upstream, inside `Semigroup-Op.interp-node` (see
[`Classical.Structures.Semigroup`][]); the bundle bridge never touches it.

```agda
⟨_⟩ˢᵍ : Semigroup α ρ → stdlib-Semigroup α ρ
⟨ 𝑺 ⟩ˢᵍ = record
  { Carrier     = 𝕌[ 𝑴 ]
  ; _≈_         = _≈_
  ; _∙_         = _∙_
  ; isSemigroup = record
      { isMagma = record { isEquivalence = isEquivalence ; ∙-cong = ∙-cong }
      ; assoc = assoc-law
      }
  }
  where
  𝑴 = semigroup→magma 𝑺
  open Semigroup-Op 𝑺
  open Setoid 𝔻[ 𝑴 ]
```

#### Stdlib bundle to core

The reverse direction reassembles the bundle's `Carrier`, `_≈_`, and `_∙_` into
an `Sig-Magma`-algebra (exactly as in the M3-3 magma bridge) and pairs that
algebra with a proof of `Th-Semigroup` extracted from the bundle's `assoc`
field by an environment-application of the same three-variable shape.

```agda
⟪_⟫ˢᵍ : stdlib-Semigroup α ρ → Semigroup α ρ
⟪ S ⟫ˢᵍ = 𝑨 , λ { assoc ρ → S-assoc (ρ 0F) (ρ 1F) (ρ 2F) }
  where
  open stdlib-Semigroup S
      using ( setoid ; ∙-cong )
      renaming ( _∙_ to _·_ ; assoc to S-assoc )

  𝑨 : Algebra _ _
  𝑨 = record { Domain = setoid ; Interp = interp }
    where
    interp : Func (⟨ Sig-Magma ⟩ setoid) setoid
    interp ⟨$⟩ (∙-Op , args) = args 0F · args 1F
    cong interp { ∙-Op , _ } { .∙-Op , _ } (≡.refl , args≈) = ∙-cong (args≈ 0F) (args≈ 1F)
```

#### Pointwise round-trip

Going core → bundle → core preserves the curried operation pointwise.  Both
sides reduce to `(∙-Op ^ 𝑺) (pair a b)` definitionally, so `Setoid.refl`
discharges the obligation.

```agda
module _ {𝑺 : Semigroup α ρ} where
  open Semigroup-Op 𝑺 ; open Setoid 𝔻[ semigroup→magma 𝑺 ]
  open Semigroup-Op ⟪ ⟨ 𝑺 ⟩ˢᵍ ⟫ˢᵍ renaming ( _∙_ to _∙'_ )

  roundtrip-cbc-sg : (a b : 𝕌[ semigroup→magma 𝑺 ]) → a ∙' b ≈ a ∙ b
  roundtrip-cbc-sg a b = refl
```

The reverse direction, bundle → core → bundle, holds pointwise on the bundle's
underlying equivalence by the same reduction.

```agda
module _ {S : stdlib-Semigroup α ρ} where
  open stdlib-Semigroup S using ( _≈_ ; _∙_ ; refl ) renaming ( Carrier to A )
  open stdlib-Semigroup ⟨ ⟪ S ⟫ˢᵍ ⟩ˢᵍ using () renaming ( _∙_ to _∙'_ )

  roundtrip-bcb-sg : (a b : A) → a ∙ b ≈ a ∙' b
  roundtrip-bcb-sg a b = refl
```
