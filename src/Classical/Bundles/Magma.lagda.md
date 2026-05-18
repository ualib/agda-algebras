---
layout: default
file: "src/Classical/Bundles/Magma.lagda.md"
title: "Classical.Bundles.Magma module"
date: "2026-05-17"
author: "the agda-algebras development team"
---

### <a id="classical-bundles-magma">Bundle bridge for magmas</a>

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

open import Agda.Primitive       using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ----------------------------
open import Algebra.Bundles                        using () renaming ( Magma to stdlib-Magma )
open import Algebra.Structures                     using (IsMagma)
open import Data.Fin.Patterns                      using ( 0F ; 1F )
open import Data.Product                           using ( _,_ )
open import Function                               using ( Func )
open import Level                                  using ( Level )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( refl )

open Setoid using (_≈_ ; isEquivalence)
open Func renaming ( to to _⟨$⟩_ )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Operations                   using ( Curry₂ ; pair )
open import Classical.Signatures.Magma             using ( Op-Magma ; ∙-Op ; Sig-Magma )
open import Classical.Structures.Magma            using ( Magma ; module Magma-Op )
open import Setoid.Algebras.Basic {𝑆 = Sig-Magma}  using ( Algebra ; _^_ ; 𝔻[_] ; 𝕌[_] ; ⟨_⟩ )
open Algebra using (Interp)

private variable α ρ : Level
```

#### <a id="core-to-bundle">Core to stdlib bundle</a>

Going from the canonical Σ-typed core to the stdlib record reads off the
domain's `Carrier` and `_≈_`, exposes the operation in curried form via
[`Classical.Structures.Magma`][]'s `_∙_`, and constructs the `IsMagma` witness
from the algebra's `Interp.cong` by unpacking the Fin 2 pattern.

```agda
⟨_⟩ₘₐ : Magma α ρ → stdlib-Magma α ρ
⟨ 𝑴 ⟩ₘₐ = let open Magma-Op 𝑴 using ( Domain ; Carrier ; _∙_ ) in
  record
  { Carrier = Carrier
  ; _≈_     = _≈_ Domain
  ; _∙_     = _∙_
  ; isMagma = record
    { isEquivalence = isEquivalence Domain
    ; ∙-cong = λ x≈y u≈v → cong (Interp 𝑴) (refl , λ { 0F → x≈y ; 1F → u≈v })
    }
  }
```

#### <a id="bundle-to-core">Stdlib bundle to core</a>

The reverse direction reassembles the bundle's `Carrier`, `_≈_`, and `_∙_` into
an `Algebra Sig-Magma`.  The interpretation of `∙-Op` uncurries the bundle's
`_∙_` by reading off `args 0F` and `args 1F`; the congruence of `Interp` is
built from the bundle's `∙-cong` applied pointwise to the argument-tuple's
equivalence proof.

```agda
⟪_⟫ₘₐ : stdlib-Magma α ρ → Magma α ρ
⟪ M ⟫ₘₐ = record
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
  cong interp { ∙-Op , _ } { .∙-Op , _ } (refl , args≈) = stdlib-Magma.∙-cong M (args≈ 0F) (args≈ 1F)
```

#### <a id="roundtrip">Pointwise round-trip</a>

Going core → bundle → core preserves the curried operation pointwise.  The two
sides reduce to the same `(∙-Op ^ 𝑴) (pair a b)` definitionally — `pair a b 0F`
and `pair a b 1F` reduce by the pattern matching in `pair` — so `Setoid.refl`
discharges the obligation.

```agda
module _ {𝑴 : Magma α ρ} where
  open Magma-Op 𝑴 using ( _∙_ )
  open Magma-Op ⟪ ⟨ 𝑴 ⟩ₘₐ ⟫ₘₐ renaming ( _∙_ to _∙'_ )

  roundtrip-cbc : (a b : Carrier) → Setoid._≈_ Domain (a ∙' b) (a ∙ b)
  roundtrip-cbc a b = Setoid.refl Domain
```

The reverse direction, bundle → core → bundle, holds pointwise on the bundle's
underlying equivalence by the same reduction.

```agda
roundtrip-bcb : (M : stdlib-Magma α ρ) (a b : stdlib-Magma.Carrier M)
  → stdlib-Magma._≈_ M (stdlib-Magma._∙_ ⟨ ⟪ M ⟫ₘₐ ⟩ₘₐ a b) (stdlib-Magma._∙_ M a b)
roundtrip-bcb M a b = stdlib-Magma.refl M
```

--------------------------------------

<span style="float:left;">[← Classical.Structures.Magma](Classical.Structures.Magma.html)</span>
<span style="float:right;">[Classical.Small.Structures.Magma →](Classical.Small.Structures.Magma.html)</span>

{% include UALib.Links.md %}
