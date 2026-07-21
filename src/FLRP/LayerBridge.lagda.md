---
layout: default
file: "src/FLRP/LayerBridge.lagda.md"
title: "FLRP.LayerBridge module (The Agda Universal Algebra Library)"
date: "2026-07-20"
author: "the agda-algebras development team"
---

### The cross-layer bridge: `Con ≅ DecCon` and `Representable ↔ Representableᵈ`

This is the [FLRP.LayerBridge][] module of the [Agda Universal Algebra Library][].

[FLRP.Problem][] states representability at the *semantic* congruence layer (Layer S,
`Con`{.AgdaFunction}) and [FLRP.Representable][] restates it at the *decidable* layer
(Layer D, `DecCon`{.AgdaFunction}); [ADR-008][] mandates that the two layers meet
through exactly one registered classical assumption, the congruence-completeness bridge
`CongruenceCompleteness`{.AgdaFunction} of [FLRP.Assumptions][].  This module discharges
that meeting.

Under the bridge as an *explicit hypothesis* we prove:

+  **`conDecIso`{.AgdaFunction}**.  The semantic congruence poset `(Con 𝑨, ≑, ⊆)` and
   the decidable congruence poset `(DecCon 𝑨, ≑ᵈ, ⊆ᵈ)` of an algebra are
   **order-isomorphic**.

   The forgetful map `DecCon → Con` (take the underlying congruence,
   `proj₁`{.AgdaFunction}) is free; its inverse `Con → DecCon` is where the bridge is
   spent; it sends a semantic congruence to a decidable representative
   `≑`{.AgdaFunction} to it.

+  **`ConIsoᵈ→ConIso`{.AgdaFunction}** / **`ConIso→ConIsoᵈ`{.AgdaFunction}**.
   A lattice order-isomorphism is transported across the layers, by composing with
   `conDecIso`{.AgdaFunction}.

   The only non-formal ingredient is that a map *into* a
   classical lattice respects the source `≑`{.AgdaFunction}.[^1]

+  **`Representableᵈ→Representable`{.AgdaFunction}** / **`Representable→Representableᵈ`{.AgdaFunction}**.
   The representability notions of the two layers are equivalent.

   `Representable`{.AgdaRecord} and `Representableᵈ`{.AgdaRecord} differ by exactly
   `ConIso`{.AgdaFunction} versus `ConIsoᵈ`{.AgdaFunction} plus the
   `finsig : FiniteSignature`{.AgdaField} datum, so each direction is an
   `OrderIso`{.AgdaRecord} transport, and the `Representable → Representableᵈ` direction
   additionally consumes the finite-signature witness (which `Representable`{.AgdaRecord}
   does not carry).

   *Both* directions consume the bridge: passing between the layers in either
   direction requires the poset isomorphism, whose `Con → DecCon` half is the
   classical step.

The `OrderIso`{.AgdaRecord} composition here is done by hand at each of the two
transports rather than through a general transitivity combinator: the round trips
need the middle lattice map to respect `≑`{.AgdaFunction} (antisymmetry), which a
fully generic `OrderIso`-transitivity cannot supply without extra hypotheses, so the
direct assembly from small named lemmas is clearer.[^2]

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.LayerBridge where

-- Imports from Agda and the Agda Standard Library -----------------------------
open import Data.Product          using ( _,_ ; proj₁ ; proj₂ )
open import Function              using ( _∘_ )
open import Level                 using ( Level ; 0ℓ ; _⊔_ )
open import Relation.Binary       using ( Setoid )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Overture                             using  ( 𝓞 ; 𝓥 ; Signature )
open import Classical.Small.Structures.Lattice   using  ( Lattice )
open import Classical.Properties.Lattice         using  ( module Lattice-Order )
open import Setoid.Algebras.Basic                using  ( Algebra ; 𝔻[_] )
open import Setoid.Signatures.Finite             using  ( FiniteSignature )
open import Setoid.Congruences.Basic             using  ( Con )
open import Setoid.Congruences.Lattice           using  ( _⊆_ ; _≑_ )
open import Setoid.Congruences.Finite.Basic      using  ( DecCon )
open import FLRP.Problem                         using  ( OrderIso ; Representable
                                                        ; ConIso )
open import FLRP.Representable                   using  ( Representableᵈ ; ConIsoᵈ
                                                        ; _⊆ᵈ_ ; _≑ᵈ_ )
open import FLRP.Assumptions                     using  ( CongruenceCompleteness )

private variable α ρ : Level
```
-->

#### The poset isomorphism `Con 𝑨 ≅ DecCon 𝑨`

Fix an algebra `𝑨`{.AgdaBound} and the bridge hypothesis `cc`{.AgdaBound}.  Working at
the absorbing congruence level `ℓw = 𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ` (the level at which
`CongruenceCompleteness`{.AgdaFunction} and the decidable layer live), the bridge gives,
for each semantic congruence `φ`{.AgdaBound}, a decidable congruence
`wit φ`{.AgdaFunction} together with a proof `wit≑`{.AgdaFunction} that `φ`{.AgdaBound}
is `≑`{.AgdaFunction} to it.

```agda
module _
  {𝑆  : Signature 𝓞 𝓥}
  {𝑨  : Algebra {𝑆 = 𝑆} α ρ}
  (cc : CongruenceCompleteness 𝑨)
  where

  private
    ℓw : Level
    ℓw = 𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ

  -- The decidable representative of a semantic congruence (the bridge's map) ...
  wit : Con 𝑨 ℓw → DecCon 𝑨 ℓw
  wit φ = proj₁ (cc φ)

  -- ... and the ≑-witness that it represents φ.
  wit≑ : (φ : Con 𝑨 ℓw) → φ ≑ proj₁ (wit φ)
  wit≑ φ = proj₂ (cc φ)
```

`wit`{.AgdaFunction} is monotone: a containment `θ ⊆ φ`{.AgdaFunction} forwards to a
containment of the representatives, because each representative is `≑`{.AgdaFunction} to
its source, so the two `≑`-witnesses bracket the given containment.

```agda
  -- wit is monotone for the containment order: the two ≑-witnesses of wit≑ bracket
  -- the given containment.  Composed with `_∘_` rather than a named ⊆-trans, whose
  -- implicit congruence arguments are not inferable through the non-injective `_⊆_`.
  wit-mono : {θ φ : Con 𝑨 ℓw} → θ ⊆ φ → wit θ ⊆ᵈ wit φ
  wit-mono {θ}{φ} θ⊆φ = wit≑ φ .proj₁ ∘ θ⊆φ ∘ wit≑ θ .proj₂
```

The order isomorphism: `to`{.AgdaFunction} is `wit`{.AgdaFunction} (the classical step),
`from`{.AgdaFunction} is `proj₁`{.AgdaFunction} (forget the decision procedure).
Forgetfulness makes `from-mono`{.AgdaFunction} the identity, since `⊆ᵈ`{.AgdaFunction} is
by definition `⊆`{.AgdaFunction} on the underlying congruences; and both round trips are
just the `≑`-witness `wit≑`{.AgdaFunction}, read in the appropriate direction.

```agda
  conDecIso : OrderIso  (_≑_ {𝑨 = 𝑨}{ℓ = ℓw}) (_⊆_ {𝑨 = 𝑨}{ℓ = ℓw})
                        (_≑ᵈ_ {𝑨 = 𝑨}{ℓ = ℓw}) (_⊆ᵈ_ {𝑨 = 𝑨}{ℓ = ℓw})
  conDecIso = record
    { to         = wit
    ; from       = proj₁
    ; to-mono    = λ {θ}{φ} → wit-mono {θ}{φ}
    ; from-mono  = λ p → p
    ; to∘from    = λ d → wit≑ (d .proj₁) .proj₂ , wit≑ (d .proj₁) .proj₁
    ; from∘to    = λ φ → wit≑ φ .proj₂ , wit≑ φ .proj₁
    }
```

#### Transporting a lattice isomorphism across the layers

Fix a classical lattice `𝑳`{.AgdaBound} and the bridge `cc`{.AgdaBound}, now at the FLRP
level discipline (`0ℓ`{.AgdaBound}).  `P`{.AgdaBound} is the poset isomorphism of the
previous section; `≈`{.AgdaFunction} is the lattice's setoid equality and `≤`{.AgdaFunction}
its meet order, whose antisymmetry `≤-antisym`{.AgdaFunction} discharges the one
`≑`-congruence obligation of each transport.

```agda
module _ {𝑆 : Signature 0ℓ 0ℓ}{𝑨 : Algebra {𝑆 = 𝑆} 0ℓ 0ℓ}
         (𝑳 : Lattice)(cc : CongruenceCompleteness 𝑨) where
  private module P = OrderIso (conDecIso cc)
  open Setoid 𝔻[ proj₁ 𝑳 ]  using ( _≈_ ) renaming ( sym to ≈sym ; trans to ≈trans )
  open Lattice-Order 𝑳       using ( _≤_ ; ≤-antisym )
```

**Layer D to Layer S**.  Given a decidable-layer isomorphism `isoᵈ : DecCon 𝑨 ≅ 𝑳`,
compose `Con → DecCon` (the `to`{.AgdaFunction} of `P`{.AgdaBound}) with it to land a
semantic-layer isomorphism `Con 𝑨 ≅ 𝑳`.  `to-cong`{.AgdaFunction} is the fact that
`isoᵈ`{.AgdaBound}'s forward map respects `≑ᵈ`{.AgdaFunction} (both images sit below one
another, and `≤`{.AgdaFunction} is antisymmetric); the round trips then chain a round
trip of `P`{.AgdaBound} (through `to-cong`{.AgdaFunction}) with one of `isoᵈ`{.AgdaBound}.

```agda
  ConIsoᵈ→ConIso : ConIsoᵈ 𝑨 𝑳 → ConIso 𝑨 𝑳
  ConIsoᵈ→ConIso isoᵈ = record
    { to         = D.to ∘ P.to
    ; from       = P.from ∘ D.from
    ; to-mono    = λ {θ}{φ} → D.to-mono ∘ P.to-mono {θ} {φ}
    ; from-mono  = λ {u}{v} → P.from-mono {D.from u} {D.from v} ∘ D.from-mono {u} {v}
    ; to∘from    = tf
    ; from∘to    = ft
    }
    where
    module D = OrderIso isoᵈ
    -- isoᵈ's forward map respects ≑ᵈ, since the meet order is antisymmetric.  (The
    -- monotone maps' endpoint implicits are forwarded only where a composition or the
    -- goal type does not already pin them — the containment relations are non-injective.)
    to-cong : {d e : DecCon 𝑨 0ℓ} → d ≑ᵈ e → D.to d ≈ D.to e
    to-cong {d}{e} deq = ≤-antisym (D.to-mono {d} {e} (deq .proj₁)) (D.to-mono {e} {d} (deq .proj₂))
    -- Con → DecCon → Con → 𝑳 collapses to 𝑳 via a P round trip (through to-cong) then an isoᵈ one.
    tf : ∀ u → D.to (P.to (P.from (D.from u))) ≈ u
    tf u = ≈trans (to-cong {P.to (P.from (D.from u))} {D.from u} (P.to∘from (D.from u))) (D.to∘from u)
    -- 𝑳 → DecCon → Con → DecCon: the ≑ round trip, composed on each ⇒-direction.
    ft : ∀ φ → P.from (D.from (D.to (P.to φ))) ≑ φ
    ft φ = P.from∘to φ .proj₁ ∘ D.from∘to (P.to φ) .proj₁
         , D.from∘to (P.to φ) .proj₂ ∘ P.from∘to φ .proj₂
```

**Layer S to Layer D**.  Dually, given a semantic-layer isomorphism
`iso : Con 𝑨 ≅ 𝑳`, compose the forgetful `DecCon → Con` (the `from`{.AgdaFunction} of
`P`{.AgdaBound}) with it.  Here `to-congᵈ`{.AgdaFunction} — that `wit`{.AgdaFunction}
(the `to`{.AgdaFunction} of `P`{.AgdaBound}) respects `≑`{.AgdaFunction} — is what the
`≑ᵈ`-valued round trip needs, and it is `wit-mono`{.AgdaFunction} in both directions.

```agda
  ConIso→ConIsoᵈ : ConIso 𝑨 𝑳 → ConIsoᵈ 𝑨 𝑳
  ConIso→ConIsoᵈ iso = record
    { to         = C.to ∘ P.from
    ; from       = P.to ∘ C.from
    ; to-mono    = λ {d}{e} → C.to-mono ∘ P.from-mono {d} {e}
    ; from-mono  = λ {u}{v} → P.to-mono {C.from u} {C.from v} ∘ C.from-mono {u} {v}
    ; to∘from    = tf
    ; from∘to    = ft
    }
    where
    module C = OrderIso iso
    -- iso's forward map respects ≑, by antisymmetry of the meet order.
    to-cong : {θ φ : Con 𝑨 0ℓ} → θ ≑ φ → C.to θ ≈ C.to φ
    to-cong {θ}{φ} eq = ≤-antisym (C.to-mono {θ} {φ} (eq .proj₁)) (C.to-mono {φ} {θ} (eq .proj₂))
    -- wit respects ≑ (needed to push an iso round trip through the ≑ᵈ side); it is
    -- P.to-mono in both directions.
    to-congᵈ : {θ φ : Con 𝑨 0ℓ} → θ ≑ φ → P.to θ ≑ᵈ P.to φ
    to-congᵈ {θ}{φ} eq = P.to-mono {θ} {φ} (eq .proj₁) , P.to-mono {φ} {θ} (eq .proj₂)
    tf : ∀ u → C.to (P.from (P.to (C.from u))) ≈ u
    tf u = ≈trans (to-cong {P.from (P.to (C.from u))} {C.from u} (P.from∘to (C.from u))) (C.to∘from u)
    -- The ≑ᵈ round trip, composed on each ⇒-direction; `cd` names the ≑ᵈ from to-congᵈ.
    ft : ∀ d → P.to (C.from (C.to (P.from d))) ≑ᵈ d
    ft d = P.to∘from d .proj₁ ∘ cd .proj₁ , cd .proj₂ ∘ P.to∘from d .proj₂
      where cd = to-congᵈ {C.from (C.to (P.from d))} {P.from d} (C.from∘to (P.from d))
```

#### The representability equivalence

The two layer-transports assemble the equivalence of the representability notions.  The
finiteness and carrier data carry over unchanged; only the isomorphism field is
transported, and `Representable → Representableᵈ`{.AgdaFunction} additionally supplies the
finite-signature witness that `Representableᵈ`{.AgdaRecord} carries and
`Representable`{.AgdaRecord} does not.

```agda
module _ {𝑳 : Lattice} where

  -- Layer D ⇒ Layer S: transport the ConIsoᵈ to a ConIso.
  Representableᵈ→Representable : (r : Representableᵈ 𝑳)
    → CongruenceCompleteness (Representableᵈ.alg r) → Representable 𝑳
  Representableᵈ→Representable r cc = record
    { sig      = Representableᵈ.sig r
    ; alg      = Representableᵈ.alg r
    ; finite   = Representableᵈ.finite r
    ; con-iso  = ConIsoᵈ→ConIso 𝑳 cc (Representableᵈ.con-isoᵈ r)
    }

  -- Layer S ⇒ Layer D: transport the ConIso to a ConIsoᵈ, given a FiniteSignature.
  Representable→Representableᵈ : (r : Representable 𝑳)
    → FiniteSignature (Representable.sig r)
    → CongruenceCompleteness (Representable.alg r) → Representableᵈ 𝑳
  Representable→Representableᵈ r fs cc = record
    { sig       = Representable.sig r
    ; alg       = Representable.alg r
    ; finite    = Representable.finite r
    ; finsig    = fs
    ; con-isoᵈ  = ConIso→ConIsoᵈ 𝑳 cc (Representable.con-iso r)
    }
```

--------------------------------------

[^1]: because the lattice meet order is antisymmetric
      (`≤-antisym`{.AgdaFunction} of [Classical.Properties.Lattice][]
      — the same one-line fact the no-go theorem of [FLRP.Problem][] uses).

[^2]: The standing FLRP research-track separation warning of [FLRP.Problem][] applies
      here too.
