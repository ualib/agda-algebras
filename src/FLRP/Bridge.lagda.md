---
layout: default
file: "src/FLRP/Bridge.lagda.md"
title: "FLRP.Bridge module (The Agda Universal Algebra Library)"
date: "2026-07-20"
author: "the agda-algebras development team"
---

### The Pálfy–Pudlák bridge (easy direction)

This is the [FLRP.Bridge][] module of the [Agda Universal Algebra Library][].

For a group `𝒢`{.AgdaBound} and a subgroup `H`{.AgdaBound}, the congruence lattice of
the transitive coset G-set `𝒢 ↷ 𝒢/H` is order-isomorphic to the interval `[H , 𝒢]`
in the subgroup lattice `Sub(𝒢)`.  This module formalizes the **easy (constructive)
direction** of the Pálfy–Pudlák correspondence — work package WP-3 of the FLRP
research program (see `docs/notes/flrp-research-roadmap.md` § 7).  Classical
references: McKenzie–McNulty–Taylor Lemma 4.20, Dixon–Mortimer Theorem 1.5A, and the
introduction of the vendored note `docs/papers/flrp/ieprops/IEProps-1205.1927v4.tex`.

The correspondence has two mutually inverse, order-preserving maps.

+  **`θ ↦ K_θ`** (`to`{.AgdaFunction}).  A congruence `θ`{.AgdaBound} of the coset
   algebra — a `G`-invariant equivalence on cosets — maps to the subgroup
   `K_θ = { g ∈ 𝒢 : H·ε ∼_θ H·g }`, the `θ`-class of the base coset viewed as a
   predicate on the carrier.  We prove `K_θ`{.AgdaFunction} is an equality-respecting
   subgroup containing `H`{.AgdaBound}, i.e. an element of the respecting interval
   `[H , 𝒢]`.
+  **`K ↦ θ_K`** (`from`{.AgdaFunction}).  A subgroup `K`{.AgdaBound} with
   `H ≤ K ≤ 𝒢` maps to the relation `H·x ∼ H·y ⟺ x ⁻¹ ∙ y ∈ K` on cosets — which is
   exactly the coset relation of `K`{.AgdaBound} from
   [Classical.Structures.Group.Cosets][].  We prove it is a congruence of the coset
   algebra (an equivalence, reflexive over `∼_H`, compatible with every unary
   translate).

The two maps are mutually inverse and monotone, giving the order isomorphism
`bridge`{.AgdaFunction}.

**On the interval side we use the respecting `UpperInterval`{.AgdaModule} of
[FLRP.Enforceable][], not the bare `SubInterval`{.AgdaModule}.**  This honors the
WP-4 finding: the round trip `to (from M) ≈ M`{.AgdaFunction} moves membership
across the setoid equality `ε ⁻¹ ∙ g ≈ g`, which is sound only because interval
elements carry a `Respects`{.AgdaFunction} proof.  Over a redundant presentation the
bare interval can be strictly larger than the respecting one, so the isomorphism is
*false* at the bare level (see the counterexample in [FLRP.Enforceable][]).

The core isomorphism `bridge`{.AgdaFunction} is the **Layer S** formulation: it relates
the *semantic* congruence lattice `Con`{.AgdaFunction} to the interval, proved
constructively with no classical or deferred hypotheses.  The correspondence itself is
layer-agnostic (ADR-008), so the **Layer D** restatement called for by the updated
acceptance criteria of issue #454 — the same isomorphism with the decidable-congruence
poset `DecCon`{.AgdaFunction} in place of `Con`{.AgdaFunction} — follows by composing
`bridge`{.AgdaFunction} with the cross-layer poset isomorphism `Con 𝑨 ≅ DecCon 𝑨` of
[FLRP.LayerBridge][].  That restatement is now provided at the end of this module
(`bridgeᵈ`{.AgdaFunction}, `interval-DecCon-representable`{.AgdaFunction}), taking the
coset algebra's congruence-completeness bridge (`CongruenceCompleteness`{.AgdaFunction}
of [FLRP.Assumptions][]) and its carrier-finiteness witness as explicit hypotheses.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.Bridge where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Patterns             using ( 0F )
open import Data.Product                  using ( _,_ ; _×_ ; Σ-syntax ; proj₁ ; proj₂ )
open import Level                         using ( Level ; 0ℓ ) renaming ( suc to lsuc )
open import Relation.Binary               using ( Setoid ; IsEquivalence )
                                          renaming ( Rel to BinaryRel )
open import Relation.Binary.Definitions   using ( _Respects_ )
open import Relation.Unary                using ( Pred ; _∈_ ; _⊆_ )

import Algebra.Properties.Group as GroupProperties

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Bundles.Group               using  ( ⟨_⟩ᵍᵖ )
open import Classical.Signatures.Unary            using  ( Sig-Unary )
open import Classical.Structures.Group.Basic      using  ( Group ; module Group-Op )
open import Classical.Structures.Group.Subgroups  using  ( IsSubgroup ; mkIsSubgroup )
open import Classical.Structures.Group.Cosets     using  ( module Coset )
open import Classical.Structures.Group.GSet       using  ( module CosetAction )
open import FLRP.Enforceable                      using  ( module UpperInterval )
open import FLRP.Problem                          using  ( OrderIso )
open import Setoid.Algebras.Basic                 using  ( Algebra ; 𝕌[_] ; 𝔻[_] ; _^_ )
open import Setoid.Algebras.Finite                using  ( FiniteAlgebra )
open import Setoid.Congruences.Basic              using  ( Con ; IsCongruence ; mkcon
                                                         ; _∣≈_ ; is-compatible
                                                         ; is-equivalence ; reflexive )
open import Setoid.Congruences.Lattice            using ( _≑_ )
                                                  renaming ( _⊆_ to _⊑_ )
open import Setoid.Congruences.Finite.Basic       using ( DecCon )
open import FLRP.Representable                     using ( _⊆ᵈ_ ; _≑ᵈ_ )
open import FLRP.Assumptions                       using ( CongruenceCompleteness )
open import FLRP.LayerBridge                       using ( conDecIso )
```
-->

#### The bridge module

The development is parameterized by a group `𝒢`{.AgdaBound} at level `0ℓ`{.AgdaBound}
and an equality-respecting subgroup `H`{.AgdaBound}, matching the level discipline of
[FLRP.Problem][] and [FLRP.Enforceable][] (`0ℓ`{.AgdaBound} suffices for every finite
instance and keeps the interval side lined up with `UpperInterval`{.AgdaModule}).

```agda
module Bridge (𝒢    : Group 0ℓ 0ℓ)
              (H    : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ)
              (H-sg : IsSubgroup 𝒢 H)
  where

  private
    𝑮 = proj₁ 𝒢
    G = 𝕌[ 𝑮 ]

  open Setoid 𝔻[ 𝑮 ]  using ( _≈_ )
                      renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open Group-Op 𝒢     using ( _∙_ ; ε ; _⁻¹ ; ∙-cong ; idˡ-law ; idʳ-law ; invˡ-law )
  open GroupProperties ⟨ 𝒢 ⟩ᵍᵖ  using ( ε⁻¹≈ε ; \\-leftDividesˡ )
  open IsSubgroup H-sg          using ( respects )
  open Coset 𝒢 H H-sg           using ( _∼_ ; ≈⇒∼ )
  open CosetAction 𝒢 H H-sg     using ( cosetAlgebra )
  open UpperInterval 𝒢 H H-sg
```

#### Elementary facts about a congruence of the coset algebra

The coset algebra's setoid equality is the coset relation `_∼_`{.AgdaFunction} of
`H`{.AgdaBound} (that is `𝔻[ cosetAlgebra ]`'s `_≈_`{.AgdaFunction}), so a congruence
`θ`{.AgdaBound} is reflexive over `_∼_`{.AgdaFunction}, and — being an equivalence
compatible with every operation symbol `g`{.AgdaBound} — it is symmetric, transitive,
and invariant under left translation `x ↦ g ∙ x`{.AgdaFunction} (the action).  These
four facts are the only structure of `θ`{.AgdaBound} the correspondence consumes.

```agda
  -- A congruence relates ∼-equal (coset-equal) elements: reflexivity over ∼_H.
  θ-refl : (θ : Con cosetAlgebra 0ℓ) {a b : G} → a ∼ b → proj₁ θ a b
  θ-refl θ = reflexive (proj₂ θ)

  -- Symmetry of the congruence.
  θ-sym : (θ : Con cosetAlgebra 0ℓ) {a b : G} → proj₁ θ a b → proj₁ θ b a
  θ-sym θ = IsEquivalence.sym (is-equivalence (proj₂ θ))

  -- Transitivity of the congruence.
  θ-trans : (θ : Con cosetAlgebra 0ℓ) {a b c : G}
    → proj₁ θ a b → proj₁ θ b c → proj₁ θ a c
  θ-trans θ = IsEquivalence.trans (is-equivalence (proj₂ θ))

  -- G-invariance: the congruence is preserved by left translation (the action of g).
  -- This is compatibility of θ with the unary operation symbol g of the coset algebra.
  θ-transl : (θ : Con cosetAlgebra 0ℓ) (g : G) {a b : G}
    → proj₁ θ a b → proj₁ θ (g ∙ a) (g ∙ b)
  θ-transl θ g {a} {b} p = is-compatible (proj₂ θ) g {λ _ → a} {λ _ → b} (λ _ → p)

  -- A single group-arithmetic fact used for the interval-side round trip.
  ε⁻¹∙ : (a : G) → ε ⁻¹ ∙ a ≈ a
  ε⁻¹∙ a = ≈trans (∙-cong ε⁻¹≈ε ≈refl) (idˡ-law a)
```

#### The forward map `θ ↦ K_θ`

`K_θ`{.AgdaFunction} is the `θ`-class of the base coset, read as a predicate on the
group carrier: `g ∈ K_θ` exactly when the identity coset `H·ε` is `θ`-related to the
coset `H·g` (in the setoid presentation, `proj₁ θ ε g`).

```agda
  -- The forward map on predicates: K_θ g  =  H·ε ∼_θ H·g.
  Kθ : (θ : Con cosetAlgebra 0ℓ) → Pred G 0ℓ
  Kθ θ g = proj₁ θ ε g
```

`K_θ`{.AgdaFunction} is a subgroup.  Each closure property is one short congruence
computation using the action laws: closure under `_∙_`{.AgdaFunction} and
`_⁻¹`{.AgdaFunction} translate the hypotheses by `x`{.AgdaBound} and `x ⁻¹`{.AgdaBound}
respectively, and re-anchor at `ε`{.AgdaFunction} through the unit and inverse laws;
containment of `ε`{.AgdaFunction} is reflexivity; and the respecting property is
transitivity against a `∼`-step.

```agda
  private
    -- ε ∈ K_θ (the identity coset is θ-related to itself).
    Kθ-ε : (θ : Con cosetAlgebra 0ℓ) → ε ∈ Kθ θ
    Kθ-ε θ = IsEquivalence.refl (is-equivalence (proj₂ θ))

    -- K_θ is closed under the group multiplication.
    Kθ-∙ : (θ : Con cosetAlgebra 0ℓ) {x y : G}
      → x ∈ Kθ θ → y ∈ Kθ θ → (x ∙ y) ∈ Kθ θ
    Kθ-∙ θ {x} {y} εx εy =
      θ-trans θ εx (θ-trans θ (θ-refl θ (≈⇒∼ (≈sym (idʳ-law x)))) (θ-transl θ x εy))

    -- K_θ is closed under inverses.
    Kθ-⁻¹ : (θ : Con cosetAlgebra 0ℓ) {x : G} → x ∈ Kθ θ → (x ⁻¹) ∈ Kθ θ
    Kθ-⁻¹ θ {x} εx = θ-sym θ
      (θ-trans θ (θ-refl θ (≈⇒∼ (≈sym (idʳ-law (x ⁻¹)))))
                 (θ-trans θ (θ-transl θ (x ⁻¹) εx) (θ-refl θ (≈⇒∼ (invˡ-law x)))))

    -- K_θ respects the setoid equality of the group.
    Kθ-resp : (θ : Con cosetAlgebra 0ℓ) → Kθ θ Respects _≈_
    Kθ-resp θ {x} {y} x≈y εx = θ-trans θ εx (θ-refl θ (≈⇒∼ x≈y))

  -- Well-definedness of the forward map (part 1): K_θ is a subgroup.
  Kθ-isSubgroup : (θ : Con cosetAlgebra 0ℓ) → IsSubgroup 𝒢 (Kθ θ)
  Kθ-isSubgroup θ = mkIsSubgroup 𝒢 (Kθ-resp θ) (Kθ-∙ θ) (Kθ-ε θ) (Kθ-⁻¹ θ)

  -- Well-definedness of the forward map (part 2): H ⊆ K_θ, so K_θ ∈ [H , 𝒢].
  -- If h ∈ H then ε ∼_H h (as ε ⁻¹ ∙ h ≈ h ∈ H), hence H·ε ∼_θ H·h by reflexivity.
  H⊆Kθ : (θ : Con cosetAlgebra 0ℓ) → H ⊆ Kθ θ
  H⊆Kθ θ {h} h∈H = θ-refl θ (respects (≈sym (ε⁻¹∙ h)) h∈H)

  -- The forward map: a congruence goes to the respecting interval element [H , K_θ].
  to : Con cosetAlgebra 0ℓ → Interval≈
  to θ = mk (Kθ θ) (Kθ-isSubgroup θ) (H⊆Kθ θ)
```

#### The backward map `K ↦ θ_K`

For an interval element `M`{.AgdaBound} with underlying subgroup `K = pred M`, the
relation `θ_K`{.AgdaFunction} is the coset relation of `K`{.AgdaBound}: cosets `H·x`
and `H·y` are `θ_K`-related exactly when `x ⁻¹ ∙ y ∈ K`.  We reuse the whole
`Coset`{.AgdaModule} infrastructure at `K`{.AgdaBound}, so its equivalence and left-
translation lemmas come for free.

```agda
  -- The backward map's relation: the coset relation of K = pred M.
  θK-rel : (M : Interval≈) → BinaryRel G 0ℓ
  θK-rel M = Coset._∼_ 𝒢 (pred M) (element-isSubgroup M)
```

`θ_K`{.AgdaFunction} is a congruence of the coset algebra of `H`{.AgdaBound}.
Reflexivity over `∼_H`{.AgdaFunction} is precisely `H ⊆ K`{.AgdaFunction} — this is
where the **upper** interval is needed: were `K`{.AgdaBound} not above
`H`{.AgdaBound}, `θ_K`{.AgdaFunction} would fail to relate `∼_H`-equal cosets, so it
would not be a congruence.  The equivalence and compatibility (with every left
translate) are the corresponding `Coset`{.AgdaModule} lemmas at `K`{.AgdaBound}.

```agda
  -- Well-definedness of the backward map: θ_K is a congruence of the coset algebra.
  θK-isCongruence : (M : Interval≈) → IsCongruence cosetAlgebra (θK-rel M)
  θK-isCongruence M = mkcon reflx equivx compatx
    where
    K   = pred M
    Ksg = element-isSubgroup M

    -- Reflexivity over ∼_H: ∼_H ⊆ ∼_K pointwise, because H ⊆ K (above M).
    reflx : {a b : G} → a ∼ b → θK-rel M a b
    reflx p = above M p

    -- θ_K is an equivalence (the Coset equivalence at K).
    equivx : IsEquivalence (θK-rel M)
    equivx = Coset.∼-isEquivalence 𝒢 K Ksg

    -- θ_K is compatible with every unary translate (left congruence at K).
    compatx : cosetAlgebra ∣≈ θK-rel M
    compatx g h = Coset.∼-congˡ 𝒢 K Ksg g (h 0F)

  -- The backward map: an interval element goes to the coset congruence θ_K.
  from : Interval≈ → Con cosetAlgebra 0ℓ
  from M = θK-rel M , θK-isCongruence M
```

#### Monotonicity of both maps

Both maps act by (co)restriction of the underlying relations, so monotonicity is
immediate: a containment of congruences forwards to a containment of the base-coset
classes, and a containment of subgroups forwards to a containment of coset relations.

```agda
  -- The forward map is monotone for the congruence containment order.
  to-mono : {θ φ : Con cosetAlgebra 0ℓ} → θ ⊑ φ → to θ ≤ᵢ to φ
  to-mono θ⊑φ p = θ⊑φ p

  -- The backward map is monotone for the interval order.
  from-mono : {M N : Interval≈} → M ≤ᵢ N → from M ⊑ from N
  from-mono M≤N p = M≤N p
```

#### Mutual inverseness

The two round trips close the correspondence.

On congruences, `θ_{K_θ} ≑ θ`: the relation `θ_{K_θ}` holds at `(x , y)` when
`H·ε ∼_θ H·(x ⁻¹ ∙ y)`, and translating by `x`{.AgdaBound} (resp. `x ⁻¹`{.AgdaBound})
re-expresses this as `H·x ∼_θ H·y` through the unit, inverse, and left-division laws.

```agda
  -- Round trip on congruences:  θ_{K_θ} ≑ θ  (mutual containment).
  from∘to : (θ : Con cosetAlgebra 0ℓ) → from (to θ) ≑ θ
  from∘to θ = fwd , bwd
    where
    -- θ_{K_θ} ⊆ θ:  from  H·ε ∼_θ H·(x ⁻¹ ∙ y)  derive  H·x ∼_θ H·y.
    fwd : from (to θ) ⊑ θ
    fwd {x} {y} q =
      θ-trans θ (θ-refl θ (≈⇒∼ (≈sym (idʳ-law x))))
                (θ-trans θ (θ-transl θ x q) (θ-refl θ (≈⇒∼ (\\-leftDividesˡ x y))))

    -- θ ⊆ θ_{K_θ}:  from  H·x ∼_θ H·y  derive  H·ε ∼_θ H·(x ⁻¹ ∙ y).
    bwd : θ ⊑ from (to θ)
    bwd {x} {y} p =
      θ-trans θ (θ-refl θ (≈⇒∼ (≈sym (invˡ-law x)))) (θ-transl θ (x ⁻¹) p)
```

On the interval, `K_{θ_K} ≈ K`: an element `g`{.AgdaBound} lies in `K_{θ_K}` when
`ε ⁻¹ ∙ g ∈ K`, and since `ε ⁻¹ ∙ g ≈ g`{.AgdaFunction} the respecting proof carried
by the interval element identifies this with `g ∈ K`.  **This is the step that
requires the respecting interval** — the sole place the correspondence would break
over the bare `SubInterval`{.AgdaModule}.

```agda
  -- Round trip on the interval:  K_{θ_K} ≈ K  (needs the respecting field).
  to∘from : (M : Interval≈) → to (from M) ≈ᵢ M
  to∘from M = fwd , bwd
    where
    -- K_{θ_K} ⊆ K:  ε ⁻¹ ∙ g ∈ K  and  ε ⁻¹ ∙ g ≈ g  give  g ∈ K.
    fwd : Kθ (from M) ⊆ pred M
    fwd {g} p = pred-respects M (ε⁻¹∙ g) p

    -- K ⊆ K_{θ_K}:  g ∈ K  and  g ≈ ε ⁻¹ ∙ g  give  ε ⁻¹ ∙ g ∈ K.
    bwd : pred M ⊆ Kθ (from M)
    bwd {g} p = pred-respects M (≈sym (ε⁻¹∙ g)) p
```

#### The order isomorphism

Assembling the four facts (two maps, both monotone, mutually inverse) yields the
Pálfy–Pudlák bridge as an `OrderIso`{.AgdaRecord} between the congruence containment
order of the coset algebra and the respecting upper interval `[H , 𝒢]`.

```agda
  -- The order isomorphism  Con (𝒢 ↷ 𝒢/H)  ≅  [H , 𝒢].
  BridgeIso : Type (lsuc 0ℓ)
  BridgeIso = OrderIso (_≑_ {𝑨 = cosetAlgebra} {ℓ = 0ℓ}) (_⊑_ {𝑨 = cosetAlgebra} {ℓ = 0ℓ}) _≈ᵢ_ _≤ᵢ_

  bridge : BridgeIso
  bridge = record
    { to        = to
    ; from      = from
    ; to-mono   = λ {θ} {φ} → to-mono {θ} {φ}
    ; from-mono = λ {M} {N} → from-mono {M} {N}
    ; to∘from   = to∘from
    ; from∘to   = from∘to
    }
```

#### Toward representability

The reverse isomorphism presents the interval `[H , 𝒢]` as the congruence lattice of
the coset algebra.

```agda
  -- The interval [H , 𝒢], order-isomorphic to Con of the coset algebra 𝑨.
  RepIso : (𝑨 : Algebra {𝑆 = Sig-Unary G} 0ℓ 0ℓ) → Type (lsuc 0ℓ)
  RepIso 𝑨 = OrderIso _≈ᵢ_ _≤ᵢ_ (_≑_ {𝑨 = 𝑨} {ℓ = 0ℓ}) (_⊑_ {𝑨 = 𝑨} {ℓ = 0ℓ})

  bridge⁻¹ : RepIso cosetAlgebra
  bridge⁻¹ = record
    { to        = from
    ; from      = to
    ; to-mono   = λ {M} {N} → from-mono {M} {N}
    ; from-mono = λ {θ} {φ} → to-mono {θ} {φ}
    ; to∘from   = from∘to
    ; from∘to   = to∘from
    }
```

**Corollary (toward representability).**  If the coset algebra is finite, then the
interval `[H , 𝒢]` is realized as the congruence lattice of a finite algebra — namely
the coset algebra itself.  The roadmap's corollary "every interval in a finite
subgroup lattice is representable" is this statement with the finiteness witness
supplied.

Finiteness of the coset algebra enters as an explicit hypothesis rather than being
derived: constructing `FiniteAlgebra cosetAlgebra`{.AgdaRecord} from finiteness of
`𝒢`{.AgdaBound} needs a decision procedure for `∼_H`{.AgdaFunction} and a surjective
enumeration of cosets, which is a separate concern.  This is exactly the datum the
decidable layer supplies: the Layer-D restatement below (`bridgeᵈ`{.AgdaFunction}) meets
`Representableᵈ`{.AgdaRecord} of the two-layer discipline (ADR-008) through this same
finiteness witness together with the congruence-completeness bridge.

```agda
  -- Corollary: a finite coset algebra realizes the interval [H , 𝒢] as its Con.
  interval-Con-representable :
    FiniteAlgebra cosetAlgebra
    → Σ[ 𝑨 ∈ Algebra {𝑆 = Sig-Unary G} 0ℓ 0ℓ ] ( FiniteAlgebra 𝑨 × RepIso 𝑨 )
  interval-Con-representable fin = cosetAlgebra , fin , bridge⁻¹
```

#### The Layer-D restatement

The updated acceptance criteria of issue #454 call for the correspondence at **Layer
D**: the same isomorphism with the *decidable* congruence poset
`DecCon`{.AgdaFunction} in place of the semantic `Con`{.AgdaFunction}.  The cross-layer
bridge of [FLRP.LayerBridge][] — the order isomorphism `Con 𝑨 ≅ DecCon 𝑨` under the
congruence-completeness assumption `CongruenceCompleteness`{.AgdaFunction} of
[FLRP.Assumptions][] — supplies exactly the missing half: composing it with
`bridge⁻¹`{.AgdaFunction} turns `[H , 𝒢] ≅ Con (𝒢 ↷ 𝒢/H)` into
`[H , 𝒢] ≅ DecCon (𝒢 ↷ 𝒢/H)`.

`RepIsoᵈ`{.AgdaFunction} is the decidable-layer analogue of `RepIso`{.AgdaFunction}:
the interval, order-isomorphic to the `DecCon`{.AgdaFunction} poset.  Its assembly
needs no antisymmetry: both round trips land in a mutual-inclusion equivalence
(`≈ᵢ`{.AgdaFunction}, `≑ᵈ`{.AgdaFunction}), so each is built directly from the two
monotone maps — the same product construction as `compose-IntervalIso`{.AgdaFunction}
of [FLRP.Enforceable][].

```agda
  RepIsoᵈ : (𝑨 : Algebra {𝑆 = Sig-Unary G} 0ℓ 0ℓ) → Type (lsuc 0ℓ)
  RepIsoᵈ 𝑨 = OrderIso _≈ᵢ_ _≤ᵢ_ (_≑ᵈ_ {𝑨 = 𝑨} {ℓ = 0ℓ}) (_⊆ᵈ_ {𝑨 = 𝑨} {ℓ = 0ℓ})

  -- bridge⁻¹ (interval ≅ Con) composed with the cross-layer poset iso
  -- (Con ≅ DecCon, under the coset algebra's congruence-completeness bridge).
  -- Endpoint implicits of the monotone maps are forwarded explicitly, and each
  -- round trip is assembled directly on a related pair — the implicit congruence
  -- arguments of the named ⊆-trans are not inferable through the non-injective
  -- containment relations (the discipline of Setoid.Congruences.Lattice).
  bridgeᵈ : CongruenceCompleteness cosetAlgebra → RepIsoᵈ cosetAlgebra
  bridgeᵈ cc = record
    { to         = λ M → CD.to (BI.to M)
    ; from       = λ d → BI.from (CD.from d)
    ; to-mono    = λ {M}{N} M≤N →
        CD.to-mono {BI.to M} {BI.to N} (BI.to-mono {M} {N} M≤N)
    ; from-mono  = λ {d}{e} d⊆e →
        BI.from-mono {CD.from d} {CD.from e} (CD.from-mono {d} {e} d⊆e)
    ; to∘from    = λ d →
          (λ p → proj₁ (CD.to∘from d)
                   (CD.to-mono {BI.to (BI.from (CD.from d))} {CD.from d}
                               (proj₁ (BI.to∘from (CD.from d))) p))
        , (λ p → CD.to-mono {CD.from d} {BI.to (BI.from (CD.from d))}
                            (proj₂ (BI.to∘from (CD.from d))) (proj₂ (CD.to∘from d) p))
    ; from∘to    = λ M →
          (λ z → proj₁ (BI.from∘to M)
                   (BI.from-mono {CD.from (CD.to (BI.to M))} {BI.to M}
                                 (proj₁ (CD.from∘to (BI.to M))) z))
        , (λ z → BI.from-mono {BI.to M} {CD.from (CD.to (BI.to M))}
                             (proj₂ (CD.from∘to (BI.to M))) (proj₂ (BI.from∘to M) z))
    }
    where
    module CD = OrderIso (conDecIso cc)
    module BI = OrderIso bridge⁻¹
```

**Corollary (Layer D, near-closing #454).**  A finite coset algebra whose semantic
congruences are all `≑`{.AgdaFunction} to decidable ones (the congruence-completeness
bridge for the coset algebra) realizes the interval `[H , 𝒢]` as its *decidable*
congruence poset.  This is the `Representableᵈ`{.AgdaRecord}-side target of the two-layer
discipline: the algebra, its carrier-finiteness witness, and the decidable-layer
isomorphism are exactly the data `Representableᵈ`{.AgdaRecord} of [FLRP.Representable][]
consumes (there over a classical `Lattice`{.AgdaRecord} presentation of the interval).

```agda
  interval-DecCon-representable :
    FiniteAlgebra cosetAlgebra
    → CongruenceCompleteness cosetAlgebra
    → Σ[ 𝑨 ∈ Algebra {𝑆 = Sig-Unary G} 0ℓ 0ℓ ] ( FiniteAlgebra 𝑨 × RepIsoᵈ 𝑨 )
  interval-DecCon-representable fin cc = cosetAlgebra , fin , bridgeᵈ cc
```
