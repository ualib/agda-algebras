---
layout: default
file: "src/Classical/Bundles/Magma.lagda.md"
title: "Classical.Bundles.Magma module"
date: "2026-05-17"
author: "the agda-algebras development team"
---

### Bundle bridge for magmas

This is the [Classical.Bundles.Magma][] module of the [Agda Universal Algebra Library][].

This module supplies the bidirectional bridge between the Σ-typed core of
[`Classical.Structures.Magma`][] and the record-typed `Algebra.Bundles.Magma`
in the Agda standard library.  Both representations carry the same mathematical
content; the bridge exists so that downstream code typed against
`Algebra.Bundles.Magma` is reusable against the canonical agda-algebras
representation without manual record-shuffling.

The round-trip is stated *pointwise* on the carrier, in the magma's underlying
setoid equivalence, per
[ADR-002 v2 §6](../../docs/adr/002-classical-layer-design.md).  The Fin 2
η-failure under `--cubical-compatible` would obstruct any propositional
`_≡_`-on-the-Σ-type formulation; the pointwise statement sidesteps it cleanly,
discharged by `Setoid.refl` because `pair a b 0F` and `pair a b 1F` reduce
definitionally to `a` and `b` respectively.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Bundles.Magma where

-- Imports from the Agda Standard Library ----------------------------
open import Algebra.Bundles                        using () renaming ( Magma to stdlib-Magma )
open import Data.Fin.Patterns                      using ( 0F ; 1F )
open import Data.Product                           using ( _,_ )
open import Function                               using ( Func )
open import Level                                  using ( Level )
open import Relation.Binary                        using ( Setoid )
import Relation.Binary.PropositionalEquality as ≡

open Func renaming ( to to _⟨$⟩_ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Signatures.Magma             using ( ∙-Op ; Sig-Magma )
open import Classical.Structures.Magma             using ( Magma ; module Magma-Op )
open import Setoid.Algebras.Basic {𝑆 = Sig-Magma}  using ( Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Signatures                      using  ( ⟨_⟩ )
open Algebra using (Interp)

private variable α ρ : Level
```

#### Core to stdlib bundle

Going from the canonical Σ-typed core to the stdlib record reads off the
domain's `Carrier` and `_≈_`, exposes the operation in curried form via
[`Classical.Structures.Magma`][]'s `_∙_`, and constructs the `IsMagma` witness
from the algebra's `Interp.cong` by unpacking the Fin 2 pattern.

```agda
⟨_⟩ᵐᵃ : Magma α ρ → stdlib-Magma α ρ
⟨ 𝑴 ⟩ᵐᵃ = record
  { Carrier = 𝕌[ 𝑴 ]
  ; _≈_     = _≈_
  ; _∙_     = _∙_
  ; isMagma = record
      { isEquivalence = isEquivalence
      ; ∙-cong = λ x≈y u≈v → cong (Interp 𝑴) (≡.refl , λ { 0F → x≈y ; 1F → u≈v })
      }
  }
  where open Magma-Op 𝑴; open Setoid 𝔻[ 𝑴 ]
```

#### Stdlib bundle to core

The reverse direction reassembles the bundle's `Carrier`, `_≈_`, and `_∙_` into
an `Algebra Sig-Magma`.  The interpretation of `∙-Op` uncurries the bundle's
`_∙_` by reading off `args 0F` and `args 1F`; the congruence of `Interp` is
built from the bundle's `∙-cong` applied pointwise to the argument-tuple's
equivalence proof.

```agda
⟪_⟫ᵐᵃ : stdlib-Magma α ρ → Magma α ρ
⟪ M ⟫ᵐᵃ = record
  { Domain = record
    { Carrier        = stdlib-Magma.Carrier M
    ; _≈_            = stdlib-Magma._≈_ M
    ; isEquivalence  = stdlib-Magma.isEquivalence M
    }
  ; Interp = interp
  }
  where
  interp : Func (⟨ Sig-Magma ⟩ (stdlib-Magma.setoid M)) (stdlib-Magma.setoid M)
  interp ⟨$⟩ (∙-Op , args) = (M stdlib-Magma.∙ (args 0F)) (args 1F)
  cong interp { ∙-Op , _ } { .∙-Op , _ } (≡.refl , args≈) = stdlib-Magma.∙-cong M (args≈ 0F) (args≈ 1F)
```

#### Pointwise round-trip

Going core → bundle → core preserves the curried operation pointwise.  The two
sides reduce to the same `(∙-Op ^ 𝑴) (pair a b)` definitionally — `pair a b 0F`
and `pair a b 1F` reduce by the pattern matching in `pair` — so `Setoid.refl`
discharges the obligation.

```agda
module _ {𝑴 : Magma α ρ} where
  open Magma-Op 𝑴 ; open Setoid 𝔻[ 𝑴 ]
  open Magma-Op ⟪ ⟨ 𝑴 ⟩ᵐᵃ ⟫ᵐᵃ renaming ( _∙_ to _∙'_ )

  roundtrip-cbc-ma : (a b : 𝕌[ 𝑴 ]) → (a ∙' b) ≈ (a ∙ b)
  roundtrip-cbc-ma a b = refl
```

The reverse direction, bundle → core → bundle, holds pointwise on the bundle's
underlying equivalence by the same reduction.

```agda
module _ {𝑴 : stdlib-Magma α ρ} where
  open stdlib-Magma 𝑴 using (_≈_; _∙_; refl) renaming (Carrier to M)
  open stdlib-Magma ⟨ ⟪ 𝑴 ⟫ᵐᵃ ⟩ᵐᵃ using () renaming ( _∙_ to _∙'_ )

  roundtrip-bcb-ma : (a b : M) → (a ∙ b) ≈ (a ∙' b)
  roundtrip-bcb-ma a b = refl
```
