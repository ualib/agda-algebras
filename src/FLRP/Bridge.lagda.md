---
layout: default
file: "src/FLRP/Bridge.lagda.md"
title: "FLRP.Bridge module (The Agda Universal Algebra Library)"
date: "2026-07-20"
author: "the agda-algebras development team"
---

### The Pálfy–Pudlák bridge (easy direction)

This is the [FLRP.Bridge][] module of the [Agda Universal Algebra Library][].

For a group `G`{.AgdaBound} and a subgroup `H`{.AgdaBound}, the congruence lattice of
the transitive coset G-set `G ↷ G/H` is order-isomorphic to the interval `[H , G]`
in the subgroup lattice `Sub G`.

This module formalizes the **easy** (constructive) **direction** of the Pálfy–Pudlák
correspondence.[^1]

The correspondence has two mutually inverse, order-preserving maps.

+  **`θ ↦ K_θ`** (`to`{.AgdaFunction}).  A congruence `θ`{.AgdaBound} of the coset
   algebra — a `G`-invariant equivalence on cosets — maps to the subgroup
   `K_θ = { g ∈ G : H·ε ∼_θ H·g }`, the `θ`-class of the base coset viewed as a
   predicate on the carrier.  We prove `K_θ`{.AgdaFunction} is an equality-respecting
   subgroup containing `H`{.AgdaBound}, i.e. an element of the respecting interval
   `[H , G]`.

+  **`K ↦ θ_K`** (`from`{.AgdaFunction}).  A subgroup `K`{.AgdaBound} with
   `H ≤ K ≤ G` maps to the relation `θ_K` on cosets defined by
   `H·x θ_K H·y ⟺ x ⁻¹ ∙ y ∈ K` — which is exactly the coset relation of
   `K`{.AgdaBound} from [Classical.Structures.Group.Cosets][].  We prove it is a
   congruence of the coset algebra (an equivalence, reflexive over `∼_H`, compatible
   with every unary translate).

The two maps are mutually inverse and monotone, giving the order isomorphism
`bridge`{.AgdaFunction}.

*On the interval side we use the respecting `UpperInterval`{.AgdaModule} of
[FLRP.Enforceable][], not the bare `SubInterval`{.AgdaModule}.*

This honors the WP-4 finding: the round trip `to (from M) ≈ M` moves
membership across the setoid equality `ε ⁻¹ ∙ g ≈ g`, which is sound only because
interval elements carry a `Respects`{.AgdaFunction} proof.

Over a redundant presentation the bare interval can be strictly larger than the
respecting one, so the isomorphism is *false* at the bare level (see the
counterexample in [FLRP.Enforceable][]).

The core isomorphism `bridge`{.AgdaFunction} is the *Layer S* formulation: it relates
the *semantic* congruence lattice `Con`{.AgdaFunction} to the interval, proved
constructively with no classical or deferred hypotheses.

The *Layer D* statement required by issue #454 is proved here as well — **directly**,
not through the classical cross-layer bridge.[^2]  The pivot is that both maps carry
their decision procedures with them: `K_θ` is the `θ`-class of the base coset, decided
by `θ`'s own decision procedure at the pair `(ε , g)`, and `θ_K` is the coset relation
of `K`, decided by one group multiplication once membership in `K`{.AgdaBound} is
decidable.  So the correspondence restricts to an order isomorphism
`bridgeᵈ`{.AgdaFunction} between the decidable congruence poset `DecCon (𝒢 ↷ 𝒢/H)` and
the *decidably presented* interval `[H , 𝒢]` (`Intervalᵈ`{.AgdaFunction} of
[FLRP.Enforceable][]), with **no classical assumption** — the congruence-completeness
bridge of [FLRP.Assumptions][] is not consumed.

The module ends with the corollaries: a finite coset algebra realizes the decidable
interval as its decidable congruence poset, and every group-representable lattice is
decidably representable (`GroupRepresentable→Representableᵈ`{.AgdaFunction}).

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.Bridge where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Patterns             using ( 0F )
open import Data.Product                  using ( _,_ ; _×_ ; Σ-syntax ; proj₁ ; proj₂ )
open import Function                      using ( _∘_ )
open import Level                         using ( 0ℓ ) renaming ( suc to lsuc )
open import Relation.Binary               using ( Setoid ; IsEquivalence )
                                          renaming ( Rel to BinaryRel )
open import Relation.Binary.Definitions   using ( _Respects_ )
open import Relation.Nullary              using ( Dec )
open import Relation.Unary                using ( Pred ; _∈_ ; _⊆_ )

import Algebra.Properties.Group as GroupProperties

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Bundles.Group               using  ( ⟨_⟩ᵍᵖ )
open import Classical.Properties.Lattice          using  ( module Lattice-Order )
open import Classical.Signatures.Unary            using  ( Sig-Unary )
open import Classical.Small.Structures.Lattice    using  ( Lattice )
open import Classical.Structures.Group.Basic      using  ( Group ; module Group-Op )
open import Classical.Structures.Group.Subgroups  using  ( IsSubgroup ; mkIsSubgroup )
open import Classical.Structures.Group.Cosets     using  ( module Coset )
open import Classical.Structures.Group.GSet       using  ( module CosetAction )
open import FLRP.Enforceable                      using  ( module UpperInterval
                                                         ; IntervalIso
                                                         ; GroupRepresentable )
open import FLRP.Problem                          using  ( OrderIso )
open import FLRP.Representable                    using  ( _⊆ᵈ_ ; _≑ᵈ_ ; ConIsoᵈ
                                                         ; Representableᵈ )
open import Setoid.Algebras.Basic                 using  ( Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Algebras.Finite                using  ( FiniteAlgebra )
open import Setoid.Congruences.Basic              using  ( Con ; IsCongruence ; mkcon
                                                         ; _∣≈_ ; is-compatible
                                                         ; is-equivalence ; reflexive )
open import Setoid.Congruences.Lattice            using  ( _≑_ )
                                                  renaming ( _⊆_ to _⊑_ )
open import Setoid.Congruences.Finite.Basic       using  ( DecCon )
open import Setoid.Signatures.Finite              using  ( FiniteSignature )
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

  𝑮 : Algebra 0ℓ 0ℓ
  𝑮 = proj₁ 𝒢
  G : Type 0ℓ
  G = 𝕌[ 𝑮 ]

  open Setoid 𝔻[ 𝑮 ]            renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
                                using ( _≈_ )
  open Group-Op 𝒢               using  ( _∙_ ; ε ; _⁻¹ ; ∙-cong ; idˡ-law
                                       ; idʳ-law ; invˡ-law )
  open GroupProperties ⟨ 𝒢 ⟩ᵍᵖ  using  ( ε⁻¹≈ε ; \\-leftDividesˡ )
  open IsSubgroup H-sg          using  ( respects )
  open Coset 𝒢 H H-sg           using  ( _∼_ ; ≈⇒∼ ; ∼-dec )
  open CosetAction 𝒢 H H-sg     using  ( cosetAlgebra ; cosetAlgebra-FiniteAlgebra )
  open UpperInterval 𝒢 H H-sg
```

#### Elementary facts about a congruence of the coset algebra

The coset algebra's setoid equality is the coset relation `_∼_`{.AgdaFunction} of
`H`{.AgdaBound} (that is `_≈_`{.AgdaFunction} of `𝔻[ cosetAlgebra ]`), so a
congruence `θ`{.AgdaBound} is reflexive over `_∼_`{.AgdaFunction}, and — being an
equivalence compatible with every operation symbol `g`{.AgdaBound} — it is symmetric,
transitive, and invariant under left translation `x ↦ g ∙ x`{.AgdaFunction} (the
action).  These four facts are the only structure of `θ`{.AgdaBound} the
correspondence consumes.

```agda
  module _ ((_θ_ , θcon) : Con cosetAlgebra 0ℓ) where

    -- A congruence relates ∼-equal (coset-equal) elements: reflexivity over ∼_H.
    θ-refl : {a b : G} → a ∼ b → a θ b
    θ-refl = reflexive θcon

    -- Symmetry of the congruence.
    θ-sym : {a b : G} → a θ b → b θ a
    θ-sym = IsEquivalence.sym (is-equivalence θcon)

    -- Transitivity of the congruence.
    θ-trans : {a b c : G} → a θ b → b θ c → a θ c
    θ-trans = IsEquivalence.trans (is-equivalence θcon)

    -- G-invariance: the congruence is preserved by left translation (the action of g).
    -- This is compatibility of θ with the unary operation symbol g of the coset algebra.
    θ-transl : (g : G) {a b : G} → a θ b → (g ∙ a) θ (g ∙ b)
    θ-transl g {a} {b} p = is-compatible θcon g {λ _ → a} {λ _ → b} (λ _ → p)

  -- A single group-arithmetic fact used for the interval-side round trip.
  ε⁻¹∙ : (a : G) → ε ⁻¹ ∙ a ≈ a
  ε⁻¹∙ a = ≈trans (∙-cong ε⁻¹≈ε ≈refl) (idˡ-law a)
```

#### The forward map `θ ↦ K_θ`

`K_θ`{.AgdaFunction} is the `θ`-class of the base coset, read as a predicate on the
group carrier: `g ∈ K_θ` exactly when the identity coset `H·ε` is `θ`-related to the
coset `H·g` (in the setoid presentation, `ε θ g`).

```agda
  -- The forward map on predicates: K_θ g  =  H·ε ∼_θ H·g.
  Kθ : (θ : Con cosetAlgebra 0ℓ) → Pred G 0ℓ
  Kθ (_θ_ , _) g = ε θ g
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
    Kθ-ε (_ , θcon) = IsEquivalence.refl (is-equivalence θcon)

    -- K_θ is closed under the group multiplication.
    Kθ-∙ : (θ : Con cosetAlgebra 0ℓ) {x y : G} → x ∈ Kθ θ → y ∈ Kθ θ → x ∙ y ∈ Kθ θ
    Kθ-∙ θ {x} {y} εx εy =
      θ-trans θ εx (θ-trans θ (θ-refl θ (≈⇒∼ (≈sym (idʳ-law x)))) (θ-transl θ x εy))

    -- K_θ is closed under inverses.
    Kθ-⁻¹ : (θ : Con cosetAlgebra 0ℓ) {x : G} → x ∈ Kθ θ → x ⁻¹ ∈ Kθ θ
    Kθ-⁻¹ θ {x} εx = θ-sym θ
      (θ-trans θ (θ-refl θ (≈⇒∼ (≈sym (idʳ-law (x ⁻¹)))))
                 (θ-trans θ (θ-transl θ (x ⁻¹) εx) (θ-refl θ (≈⇒∼ (invˡ-law x)))))

    -- K_θ respects the setoid equality of the group.
    Kθ-resp : (θ : Con cosetAlgebra 0ℓ) → Kθ θ Respects _≈_
    Kθ-resp θ x≈y εx = θ-trans θ εx (θ-refl θ (≈⇒∼ x≈y))

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
  θK-rel M = Coset._∼_ 𝒢 (set M) (element-isSubgroup M)
```

`θ_K`{.AgdaFunction} is a congruence of the coset algebra of `H`{.AgdaBound}.
Reflexivity over `∼_H`{.AgdaFunction} is precisely `H ⊆ K`{.AgdaFunction} — this is
where the **upper** interval is needed: were `K`{.AgdaBound} not above
`H`{.AgdaBound}, `θ_K`{.AgdaFunction} would fail to relate `∼_H`-equal cosets, so it
would not be a congruence.  The equivalence and compatibility (with every left
translate) are the corresponding `Coset`{.AgdaModule} lemmas at `K`{.AgdaBound}.

```agda
  -- Well-definedness of the backward map: θ_K is a congruence of the coset algebra.
  θK-isCongruence : (𝑴 : Interval≈) → IsCongruence cosetAlgebra (θK-rel 𝑴)
  θK-isCongruence 𝑴@(((M , _) , H≤M , _) , _) = mkcon reflx equivx compatx
    where

    Ksg : IsSubgroup 𝒢 M
    Ksg = element-isSubgroup 𝑴

    -- Reflexivity over ∼_H: ∼_H ⊆ ∼_K pointwise, because H ⊆ K (above M).
    reflx : {a b : G} → a ∼ b → θK-rel 𝑴 a b
    reflx = H≤M

    -- θ_K is an equivalence (the Coset equivalence at K).
    equivx : IsEquivalence (θK-rel 𝑴)
    equivx = Coset.∼-isEquivalence 𝒢 M Ksg

    -- θ_K is compatible with every unary translate (left congruence at K).
    compatx : cosetAlgebra ∣≈ θK-rel 𝑴
    compatx g h = Coset.∼-congˡ 𝒢 M Ksg g (h 0F)

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
    fwd : Kθ (from M) ⊆ set M
    fwd {g} p = set-respects M (ε⁻¹∙ g) p

    -- K ⊆ K_{θ_K}:  g ∈ K  and  g ≈ ε ⁻¹ ∙ g  give  ε ⁻¹ ∙ g ∈ K.
    bwd : set M ⊆ Kθ (from M)
    bwd {g} p = set-respects M (≈sym (ε⁻¹∙ g)) p
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
rederived here: `cosetAlgebra-FiniteAlgebra`{.AgdaFunction} of
[Classical.Structures.Group.GSet][] discharges it constructively from finiteness of
`𝒢`{.AgdaBound} plus decidability of `∼_H`{.AgdaFunction} — that is, of membership in
`H`{.AgdaBound}, by `∼-dec`{.AgdaFunction} of [Classical.Structures.Group.Cosets][].
The Layer-D development below meets `Representableᵈ`{.AgdaRecord} of the two-layer
discipline (ADR-008) through this same finiteness witness, with no classical
assumption.

```agda
  -- Corollary: a finite coset algebra realizes the interval [H , 𝒢] as its Con.
  interval-Con-representable :
    FiniteAlgebra cosetAlgebra
    → Σ[ 𝑨 ∈ Algebra {𝑆 = Sig-Unary G} 0ℓ 0ℓ ] ( FiniteAlgebra 𝑨 × RepIso 𝑨 )
  interval-Con-representable fin = cosetAlgebra , fin , bridge⁻¹
```

#### The Layer-D correspondence, directly and constructively

The updated acceptance criteria of issue #454 call for the correspondence at **Layer
D**: the same isomorphism with the *decidable* congruence poset `DecCon`{.AgdaFunction}
in place of the semantic `Con`{.AgdaFunction}.  No classical assumption is needed,
because the two maps of the Layer-S bridge already *carry* decision procedures.

+  **Forward**.  `K_θ` is the `θ`-class of the base coset, so a decidable congruence
   decides membership in its own image: run its decision procedure at `(ε , g)`.
+  **Backward**.  `θ_K` is the coset relation of `K`, so a membership decider for
   `K`{.AgdaBound} decides `θ_K` after one group multiplication —
   `∼-dec`{.AgdaFunction} of [Classical.Structures.Group.Cosets][], instantiated at
   `K`{.AgdaBound}.

On the interval side the decidable layer quantifies over the *decidably presented*
interval `Intervalᵈ`{.AgdaFunction} of [FLRP.Enforceable][] — interval elements
bundled with membership deciders — exactly as the congruence side quantifies over
`DecCon`{.AgdaFunction} rather than `Con`{.AgdaFunction}.  This is a necessity, not a
convenience: over the bare interval the Layer-D isomorphism would be as
non-constructive as the Layer-S one, since an interval element can encode an arbitrary
proposition in its membership predicate and the round trip would decide it — the
oracle obstruction of the WP-1 no-go theorem, in interval clothing (see the footnote
to `Intervalᵈ`{.AgdaFunction}).

```agda
  -- Forward decidability: a decidable congruence decides membership in K_θ by
  -- running its own decision procedure at the pair (ε , g).
  Kθ-dec : (d : DecCon cosetAlgebra 0ℓ) (g : G) → Dec (g ∈ Kθ (d .proj₁))
  Kθ-dec d g = d .proj₂ ε g

  -- Backward decidability: θ_K is the coset relation of K = set M, so a membership
  -- decider for K decides it by a single group multiplication.
  θK-dec : (M : Interval≈) → (∀ x → Dec (x ∈ set M)) → ∀ x y → Dec (θK-rel M x y)
  θK-dec M = Coset.∼-dec 𝒢 (set M) (element-isSubgroup M)
```

The two maps of the decidable layer are the Layer-S maps, each paired with its
decision procedure.

```agda
  -- The forward map at Layer D: K_θ together with its decision procedure.
  toᵈ : DecCon cosetAlgebra 0ℓ → Intervalᵈ
  toᵈ d = to (d .proj₁) , Kθ-dec d

  -- The backward map at Layer D: θ_K together with its decision procedure.
  fromᵈ : Intervalᵈ → DecCon cosetAlgebra 0ℓ
  fromᵈ M = from (M .proj₁) , θK-dec (M .proj₁) (M .proj₂)
```

The Layer-D equivalences and orders on the two sides (`≑ᵈ`{.AgdaFunction},
`⊆ᵈ`{.AgdaFunction}; `≈ᵢᵈ`{.AgdaFunction}, `≤ᵢᵈ`{.AgdaFunction}) compare the
*underlying* congruences and interval elements, so the monotonicity and round-trip
proofs of the Layer-S bridge transport verbatim — nothing is reproved.  (The endpoint
implicits of the monotone maps are forwarded explicitly, per the non-injectivity
discipline of [Setoid.Congruences.Lattice][].)

```agda
  -- The Layer-D order isomorphism  DecCon (𝒢 ↷ 𝒢/H)  ≅  [H , 𝒢]ᵈ  — with no
  -- classical assumption.
  BridgeIsoᵈ : Type (lsuc 0ℓ)
  BridgeIsoᵈ = OrderIso  (_≑ᵈ_ {𝑨 = cosetAlgebra} {ℓ = 0ℓ}) (_⊆ᵈ_ {𝑨 = cosetAlgebra} {ℓ = 0ℓ})
                         _≈ᵢᵈ_ _≤ᵢᵈ_

  bridgeᵈ : BridgeIsoᵈ
  bridgeᵈ = record
    { to         = toᵈ
    ; from       = fromᵈ
    ; to-mono    = λ {d} {e} → to-mono {d .proj₁} {e .proj₁}
    ; from-mono  = λ {M} {N} → from-mono {M .proj₁} {N .proj₁}
    ; to∘from    = λ M → to∘from (M .proj₁)
    ; from∘to    = λ d → from∘to (d .proj₁)
    }
```

The reverse isomorphism presents the decidable interval as the decidable congruence
poset of the coset algebra — the Layer-D analogue of `bridge⁻¹`{.AgdaFunction}.

```agda
  RepIsoᵈ : (𝑨 : Algebra {𝑆 = Sig-Unary G} 0ℓ 0ℓ) → Type (lsuc 0ℓ)
  RepIsoᵈ 𝑨 = OrderIso _≈ᵢᵈ_ _≤ᵢᵈ_ (_≑ᵈ_ {𝑨 = 𝑨} {ℓ = 0ℓ}) (_⊆ᵈ_ {𝑨 = 𝑨} {ℓ = 0ℓ})

  bridgeᵈ⁻¹ : RepIsoᵈ cosetAlgebra
  bridgeᵈ⁻¹ = record
    { to         = fromᵈ
    ; from       = toᵈ
    ; to-mono    = λ {M} {N} → from-mono {M .proj₁} {N .proj₁}
    ; from-mono  = λ {d} {e} → to-mono {d .proj₁} {e .proj₁}
    ; to∘from    = λ d → from∘to (d .proj₁)
    ; from∘to    = λ M → to∘from (M .proj₁)
    }
```

**Corollary** (Layer D).[^3]  A finite coset algebra realizes the decidable interval
`[H , 𝒢]ᵈ` as its decidable congruence poset — unconditionally.  The finiteness
witness is itself discharged constructively by
`cosetAlgebra-FiniteAlgebra`{.AgdaFunction} whenever membership in `H`{.AgdaBound} is
decidable.

```agda
  interval-DecCon-representable :
    FiniteAlgebra cosetAlgebra
    → Σ[ 𝑨 ∈ Algebra {𝑆 = Sig-Unary G} 0ℓ 0ℓ ] ( FiniteAlgebra 𝑨 × RepIsoᵈ 𝑨 )
  interval-DecCon-representable fin = cosetAlgebra , fin , bridgeᵈ⁻¹
```

#### Composing with an interval isomorphism

The representability corollary must turn an interval isomorphism `[H , 𝒢] ≅ 𝑳` — an
`IntervalIso`{.AgdaFunction} of [FLRP.Enforceable][], stated over the bare respecting
interval — into a decidable-layer congruence isomorphism `ConIsoᵈ cosetAlgebra 𝑳` of
[FLRP.Representable][].  The composition follows `compose-IntervalIso`{.AgdaFunction}
of [FLRP.Enforceable][]: the interval-equality round trip is pushed through the
lattice-valued map by the meet order's antisymmetry, and through the
congruence-valued map by monotonicity.

One datum is needed beyond the isomorphism itself: a membership decider for each
interval element in the image of the isomorphism's backward map, so that the
composite's backward map lands in `DecCon`{.AgdaFunction}.  Per the discussion above
this is genuinely data — part of the Layer-D presentation of the representation, like
decidable membership in `H`{.AgdaBound} itself — not derivable from finiteness.

```agda
  IntervalIso→ConIsoᵈ :
    (𝑳 : Lattice) (iso : IntervalIso 𝒢 H H-sg 𝑳)
    → (∀ u x → Dec (x ∈ set (OrderIso.from iso u)))
    → ConIsoᵈ cosetAlgebra 𝑳
  IntervalIso→ConIsoᵈ 𝑳 iso from-dec = record
    { to         = to'
    ; from       = from'
    ; to-mono    = λ {d} {e} → I.to-mono ∘ to-mono {d .proj₁} {e .proj₁}
    ; from-mono  = λ {u} {v} → from-mono {I.from u} {I.from v} ∘ I.from-mono {u} {v}
    ; to∘from    = tf
    ; from∘to    = ft
    }
    where
    module I = OrderIso iso
    open Setoid 𝔻[ proj₁ 𝑳 ]  using () renaming ( _≈_ to _≈ᴸ_ ; trans to ≈ᴸ-trans )
    open Lattice-Order 𝑳       using () renaming ( ≤-antisym to ≤ᴸ-antisym )

    to' : DecCon cosetAlgebra 0ℓ → 𝕌[ proj₁ 𝑳 ]
    to' d = I.to (to (d .proj₁))

    from' : 𝕌[ proj₁ 𝑳 ] → DecCon cosetAlgebra 0ℓ
    from' u = fromᵈ (I.from u , from-dec u)

    -- 𝑳 → DecCon → 𝑳: a bridge round trip pushed through I.to by antisymmetry,
    -- then an iso round trip.
    tf : ∀ u → to' (from' u) ≈ᴸ u
    tf u = ≈ᴸ-trans
      (≤ᴸ-antisym  (I.to-mono (to∘from (I.from u) .proj₁))
                   (I.to-mono (to∘from (I.from u) .proj₂)))
      (I.to∘from u)

    -- DecCon → 𝑳 → DecCon: an iso round trip pushed through `from` by
    -- monotonicity, then a bridge round trip, composed on each ⇒-direction.
    ft : ∀ d → from' (to' d) ≑ᵈ d
    ft d =
        from∘to (d .proj₁) .proj₁ ∘
          from-mono {I.from (to' d)} {to (d .proj₁)} (I.from∘to (to (d .proj₁)) .proj₁)
      , from-mono {to (d .proj₁)} {I.from (to' d)} (I.from∘to (to (d .proj₁)) .proj₂) ∘
          from∘to (d .proj₁) .proj₂
```

#### From group representability to decidable representability

The headline corollary of issue #454: a lattice that occurs as an upper interval
`[H , 𝒢]` in a subgroup lattice (`GroupRepresentable`{.AgdaRecord} of
[FLRP.Enforceable][]) is decidably representable (`Representableᵈ`{.AgdaRecord} of
[FLRP.Representable][]), the representing finite algebra being the coset algebra
`𝒢 ↷ 𝒢/H` of the witnessing representation.

The hypotheses are exactly the Layer-D presentation data of the witness, per audit A2
(`docs/notes/flrp-wp7-audits.md`):

+  carrier finiteness of the group, as a `FiniteAlgebra`{.AgdaRecord} witness;
+  finite-finitariness of the unary signature on the group's carrier — built from an
   `≡`-surjective enumeration of the carrier by
   `Sig-Unary-FiniteSignature`{.AgdaFunction} of [Classical.Signatures.Finite][]
   (surjectivity up to `≈` does not suffice for a *signature*; see the caveat there);
+  a membership decider for `H`{.AgdaBound};
+  membership deciders for the interval elements in the image of the interval
   isomorphism's backward map.

None of these is classical, and all are inhabited by the concrete finite groups the
FLRP program ranges over (Cayley-table groups with decidable subgroup predicates).

```agda
module _ (𝑳 : Lattice) (rep : GroupRepresentable 𝑳) where
  open GroupRepresentable rep   -- grp , sub , isSubgroup , interval-iso

  private
    module B   = Bridge grp sub isSubgroup
    module UI  = UpperInterval grp sub isSubgroup
    module I   = OrderIso interval-iso

  open CosetAction grp sub isSubgroup  using ( cosetAlgebra ; cosetAlgebra-FiniteAlgebra )
  open Coset grp sub isSubgroup        using ( ∼-dec )

  -- Every group-representable lattice is decidably representable, via the coset
  -- algebra of the witnessing representation.
  GroupRepresentable→Representableᵈ :
       FiniteAlgebra (grp .proj₁)
    →  FiniteSignature (Sig-Unary 𝕌[ grp .proj₁ ])
    →  (∀ x → Dec (x ∈ sub))
    →  (∀ u x → Dec (x ∈ UI.set (I.from u)))
    →  Representableᵈ 𝑳
  GroupRepresentable→Representableᵈ fin finsig sub-dec from-dec = record
    { sigᵈ      = Sig-Unary 𝕌[ grp .proj₁ ]
    ; algᵈ      = cosetAlgebra
    ; finiteᵈ   = cosetAlgebra-FiniteAlgebra fin (∼-dec sub-dec)
    ; finsigᵈ   = finsig
    ; con-isoᵈ  = B.IntervalIso→ConIsoᵈ 𝑳 interval-iso from-dec
    }
```

---

[^1]: This is the main deliverable of work package WP-3;
      see [`docs/notes/flrp-research-roadmap.md`](docs/notes/flrp-research-roadmap.md) § 7.
      Classical references include McKenzie–McNulty–Taylor Lemma 4.20, Dixon–Mortimer
      Theorem 1.5A, and the introduction of the research note
      [`docs/papers/flrp/ieprops/IEProps-1205.1927v4.tex`](docs/papers/flrp/ieprops/IEProps-1205.1927v4.tex).

[^2]: An earlier revision of this module reached Layer D by composing
      `bridge⁻¹`{.AgdaFunction} with the cross-layer isomorphism `Con 𝑨 ≅ DecCon 𝑨`
      of [FLRP.LayerBridge][], which consumes the registered classical assumption
      `CongruenceCompleteness`{.AgdaFunction} of [FLRP.Assumptions][].  The direct
      construction below supersedes that composition: stated over the decidably
      presented interval, the correspondence needs no assumption at all, which is
      what the acceptance criteria of Issue #454 require.  The generic cross-layer
      transports remain available in [FLRP.LayerBridge][] for results that genuinely
      live at Layer S.

[^3]: This Corollary, together with `GroupRepresentable→Representableᵈ`{.AgdaFunction}
      at the end of the module, closes
      [Issue #454](https://github.com/ualib/agda-algebras/issues/454).
