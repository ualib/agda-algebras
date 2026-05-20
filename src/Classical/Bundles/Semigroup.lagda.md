---
layout: default
file: "src/Classical/Bundles/Semigroup.lagda.md"
title: "Classical.Bundles.Semigroup module"
date: "2026-05-18"
author: "the agda-algebras development team"
---

### <a id="classical-bundles-semigroup">Bundle bridge for semigroups</a>

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
nothing new to the bridge's obstruction analysis, only to its content.

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
open import Classical.Signatures.Magma      using ( ∙-Op ; Sig-Magma )
open import Classical.Structures.Magma      using ( Magma ; module Magma-Op )
open import Classical.Structures.Semigroup  using ( Semigroup ; semigroup→magma ; module Semigroup-Op )
open import Classical.Theories.Semigroup    using ( assoc )

open import Setoid.Algebras.Basic {𝑆 = Sig-Magma} using ( Algebra ; ⟨_⟩ ; 𝕌[_] ; 𝔻[_] )

open Algebra using ( Interp )

private variable α ρ : Level
```

#### <a id="core-to-bundle">Core to stdlib bundle</a>

Going from the canonical Σ-typed core to the stdlib record reads off the
domain's `Carrier` and `_≈_`, exposes the operation in curried form via
[`Classical.Structures.Semigroup`][]'s `Semigroup-Op`, builds the `isMagma`
witness from the algebra's `Interp.cong` the same way the M3-3 bridge does, and
discharges `assoc` by applying the `equations` accessor to the three-variable
environment `λ { 0F → a ; 1F → b ; 2F → c }`.

```agda
⟨_⟩ˢᵍ : Semigroup α ρ → stdlib-Semigroup α ρ
⟨ 𝑺 ⟩ˢᵍ = record
  { Carrier     = 𝕌[ 𝑴 ]
  ; _≈_         = _≈_
  ; _∙_         = _∙_
  ; isSemigroup = record
      { isMagma = record
          { isEquivalence = isEquivalence
          ; ∙-cong = λ x≈y u≈v →
              cong (Interp 𝑴) (≡.refl , λ { 0F → x≈y ; 1F → u≈v })
          }
      -- `equations assoc η` proves associativity in term-interpretation form:
      --     `⟦ lhsT ⟧ ⟨$⟩ η` / `⟦ rhsT ⟧ ⟨$⟩ η`.
      -- The stdlib `assoc` field wants it in curried form:
      --     `(a ∙ b) ∙ c` / `a ∙ (b ∙ c)`.
      -- These differ only by the Fin 2 η-gap inside each `∙-Op` node: interpretation
      -- yields a stuck `λ i → ⟦ pair _ _ i ⟧ ⟨$⟩ η` argument tuple where the
      -- curried form has `pair (a ∙ b) c`.  The two `cong (Interp 𝑴)` sandwiches
      -- bridge that gap pointwise — `refl` at the leaves, one nested `cong` at
      -- the compound subterm — exactly as `∙-cong` does one level up.
      ; assoc = λ a b c →
          trans (sym (cong (Interp 𝑴)
                  (≡.refl , λ { 0F → cong (Interp 𝑴) (≡.refl , λ { 0F → refl ; 1F → refl })
                              ; 1F → refl })))
          ( trans (equations assoc (λ { 0F → a ; 1F → b ; 2F → c }))
                  (cong (Interp 𝑴)
                    (≡.refl , λ { 0F → refl
                                ; 1F → cong (Interp 𝑴) (≡.refl , λ { 0F → refl ; 1F → refl }) })) )
      }
  }
  where
  𝑴 = semigroup→magma 𝑺
  open Semigroup-Op 𝑺
  open Setoid 𝔻[ 𝑴 ]
```

#### <a id="bundle-to-core">Stdlib bundle to core</a>

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
    interp ⟨$⟩ (∙-Op , args)                                = args 0F · args 1F
    cong interp { ∙-Op , _ } { .∙-Op , _ } (≡.refl , args≈) = ∙-cong (args≈ 0F) (args≈ 1F)
```

#### <a id="roundtrip">Pointwise round-trip</a>

Going core → bundle → core preserves the curried operation pointwise.  Both
sides reduce to `(∙-Op ^ 𝑺) (pair a b)` definitionally, so `Setoid.refl`
discharges the obligation.

```agda
module _ {𝑺 : Semigroup α ρ} where
  open Semigroup-Op 𝑺 ; open Setoid 𝔻[ semigroup→magma 𝑺 ]
  open Semigroup-Op ⟪ ⟨ 𝑺 ⟩ˢᵍ ⟫ˢᵍ renaming ( _∙_ to _∙'_ )

  roundtrip-cbc : (a b : 𝕌[ semigroup→magma 𝑺 ]) → (a ∙' b) ≈ (a ∙ b)
  roundtrip-cbc a b = refl
```

The reverse direction, bundle → core → bundle, holds pointwise on the bundle's
underlying equivalence by the same reduction.

```agda
module _ {S : stdlib-Semigroup α ρ} where
  open stdlib-Semigroup S using ( _≈_ ; _∙_ ; refl ) renaming ( Carrier to A )
  open stdlib-Semigroup ⟨ ⟪ S ⟫ˢᵍ ⟩ˢᵍ using () renaming ( _∙_ to _∙'_ )

  roundtrip-bcb : (a b : A) → (a ∙ b) ≈ (a ∙' b)
  roundtrip-bcb a b = refl
```

--------------------------------------

<span style="float:left;">[← Classical.Structures.Semigroup](Classical.Structures.Semigroup.html)</span>
<span style="float:right;">[Classical.Small.Structures.Semigroup →](Classical.Small.Structures.Semigroup.html)</span>

{% include UALib.Links.md %}
