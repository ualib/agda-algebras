---
layout: default
file: "src/Classical/Structures/Group/Congruences.lagda.md"
title: "Classical.Structures.Group.Congruences module"
date: "2026-07-26"
author: "the agda-algebras development team"
---

### Normal subgroups and congruences of a group

This is the [Classical.Structures.Group.Congruences][] module of the [Agda Universal Algebra Library][].

For a group `𝒢`{.AgdaBound}, the congruences of the underlying `Sig-Group`-algebra and
the normal subgroups of `𝒢`{.AgdaBound} are the same thing.  This module proves it, as
an order isomorphism `Con 𝑮 ℓ ≅ NormalSubgroup ℓ`{.AgdaFunction}, and identifies the
congruence-side notion of a **nonzero** congruence with the subgroup-side notion of a
**nontrivial** normal subgroup.

The correspondence has two mutually inverse, order-preserving maps.

+  **`N ↦ θ_N`** (`congruenceOf`{.AgdaFunction}).  A normal subgroup `N`{.AgdaBound}
   maps to the relation `NormalRel N`{.AgdaFunction}, defined by
   `x θ_N y ⟺ x ∙ y ⁻¹ ∈ N`.  We prove it is an equivalence containing the setoid
   equality — for that, `N`{.AgdaBound} being an equality-respecting subgroup is
   enough — and that it is compatible with the three operations of
   `Sig-Group`{.AgdaFunction}, which is where normality is consumed.

+  **`θ ↦ N_θ`** (`normalOf`{.AgdaFunction}).  A congruence `θ`{.AgdaBound} maps to
   the `θ`-class of the identity — `IdentityClass`{.AgdaFunction} `θ`{.AgdaBound}, the
   predicate `{ x ∣ x θ ε }`.  We prove it is an equality-respecting subgroup and that
   it is normal.

The two maps are monotone and mutually inverse — up to `≑`{.AgdaFunction} on
congruences and mutual inclusion on normal subgroups — so together they are an
`OrderIso`{.AgdaRecord} of [Order.Iso][].

This is the bridge that `Classical.Structures.Group.MinimalNormal` was written
without: it lets the library's `IsSubdirectlyIrreducible`{.AgdaFunction} of
[Setoid.Congruences.Monolith][] — a statement about `Con 𝑨`{.AgdaFunction} — be applied
to a group, whose subdirect irreducibility the group theorist states as "there is a
least nontrivial normal subgroup".  The final step of that identification,
`HasMonolithᵍ → HasMonolith`, is deliberately *not* taken here; see **What this module
does not do** below.

Four points about the formal statement deserve to be recorded up front, because in each
case the informal slogan "congruences are normal subgroups" conceals a choice that the
mechanized version has to make.

+  **The correspondence is level-uniform, not level-collapsing**.  It is an
   isomorphism `Con 𝑮 ℓ ≅ NormalSubgroup ℓ`{.AgdaFunction} for each *fixed* relation
   level `ℓ`{.AgdaBound}, since `NormalRel`{.AgdaFunction} of a `Pred G ℓ` is a
   `BinaryRel G ℓ` and `IdentityClass`{.AgdaFunction} of a `Con 𝑮 ℓ` is a `Pred G ℓ`.
   It says nothing about congruences at one level versus normal subgroups at another.
   The instance the monolith needs is `ℓ = ρ`, where the congruence side is the `Con 𝑮 ρ`
   of `IsMonolith`{.AgdaRecord} and the subgroup side contains
   `trivialSubgroup`{.AgdaFunction}, itself a `Subgroup ρ`.  A consumer that wants to
   compose with the subgroup *lattice* must instead take `ℓ = α ⊔ ℓ₀`, the predicate
   level `L` at which `GroupSublattice 𝒢 ℓ₀`{.AgdaModule} of
   [Classical.Structures.Group.SubgroupLattice][] holds its elements.

+  **Equality on each side is mutual containment, not propositional equality**.  On the
   congruence side this is `_≑_`{.AgdaFunction} of [Setoid.Congruences.Lattice][], for
   the reasons given there (upgrading it would need propositional extensionality, which
   `--safe --cubical-compatible` does not provide); on the subgroup side we take the
   matching `_≈ⁿ_`{.AgdaFunction}.  So `to∘from`{.AgdaField} and `from∘to`{.AgdaField}
   are *bi-implications of membership*, not equalities of predicates.

+  **The round trip on subgroups uses the `respects`{.AgdaField} field**.  Recovering
   `N`{.AgdaBound} from `θ_N` produces `{ x ∣ x ∙ ε ⁻¹ ∈ N }`, and identifying that with
   `N`{.AgdaBound} moves membership across `x ∙ ε ⁻¹ ≈ x`.  A normal *subuniverse* that
   does not respect the setoid equality therefore need not be recovered by the round
   trip, exactly as in the respecting-interval finding of [FLRP.Bridge][].  This is why
   `NormalSubgroup`{.AgdaFunction} is built on `IsSubgroup`{.AgdaRecord} (which carries
   `respects`{.AgdaField}) rather than on bare `Subuniverses`{.AgdaFunction}.

+  **Normality is consumed only by compatibility, and it is consumed exactly**.  For an
   arbitrary equality-respecting subgroup `N`{.AgdaBound}, `NormalRel N`{.AgdaFunction}
   is already an equivalence relation containing `_≈_`{.AgdaFunction}; this is
   `SubgroupRel`{.AgdaModule} below, and it holds with no normality hypothesis.  What
   needs normality is compatibility with `∙-Op`{.AgdaInductiveConstructor} and
   `⁻¹-Op`{.AgdaInductiveConstructor}, so the separation is stated rather than folded
   into one monolithic lemma — and the converse `congruence→normal`{.AgdaFunction} is
   proved, so that "the correspondence is with the *normal* subgroups" is a theorem of
   the module and not a claim its prose makes on the development's behalf.

**On the choice of relation.**  `x ∙ y ⁻¹ ∈ N` is the *right*-coset relation of
`N`{.AgdaBound}, whereas `Coset._∼_`{.AgdaFunction} of
[Classical.Structures.Group.Cosets][] — the relation [FLRP.Bridge][] uses — is the
*left*-coset relation `x ⁻¹ ∙ y ∈ N`.  For a general subgroup the two need not agree;
for a normal subgroup they do, which we prove (`rel→coset`{.AgdaFunction},
`coset→rel`{.AgdaFunction}) rather than assume, so that either presentation may be used
downstream.

**What this module does not do.**  Issue #508 also asks that
`HasMonolithᵍ`{.AgdaFunction} of `Classical.Structures.Group.MinimalNormal` be
transported to `HasMonolith`{.AgdaFunction}, that the `ᵍ` superscript be retired, and
that `𝒢₂` of `FLRP.Reductions` be restated.  Those steps are held back until the pull
request that introduces `MinimalNormal` lands; everything above is independent of them.
The `Nonzero`{.AgdaFunction}/nontriviality equivalences proved here
(`nonzero→nontrivial`{.AgdaFunction} and friends) are precisely the ingredient that
transport will need beyond the isomorphism itself.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.Congruences where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Patterns             using  ( 0F ; 1F )
open import Data.Product                  using  ( _,_ ; _×_ ; Σ-syntax
                                                 ; proj₁ ; proj₂ )
open import Level                         using  ( Level ; _⊔_ ; suc )
open import Relation.Binary               using  ( Setoid ; IsEquivalence )
                                          renaming ( Rel to BinaryRel )
open import Relation.Binary.Definitions   using  ( _Respects_ )
open import Relation.Nullary              using  ( ¬_ )
open import Relation.Unary                using  ( Pred ; _∈_ ; _⊆_ )

import Algebra.Properties.Group as GroupProperties
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Bundles.Group                 using  ( ⟨_⟩ᵍᵖ )
open import Classical.Operations                    using  ( pair )
open import Classical.Signatures.Group              using  ( ∙-Op ; ε-Op ; ⁻¹-Op )
open import Classical.Structures.Group.Basic        using  ( Group ; module Group-Op )
open import Classical.Structures.Group.Conjugation  using  ( module Conj )
open import Classical.Structures.Group.Cosets       using  ( module Coset )
open import Classical.Structures.Group.Subgroups    using  ( IsSubgroup ; mkIsSubgroup
                                                           ; trivialSubgroup
                                                           ; interp-tuple-∙
                                                           ; interp-tuple-ε
                                                           ; interp-tuple-⁻¹ )
open import Order.Iso                               using  ( OrderIso )
open import Setoid.Algebras.Basic                   using  ( 𝕌[_] ; 𝔻[_] )
open import Setoid.Congruences.Basic                using  ( Con ; IsCongruence ; mkcon
                                                           ; _∣≈_ ; is-compatible
                                                           ; is-equivalence ; reflexive )
open import Setoid.Congruences.Lattice              using  ( _≑_ )
                                                    renaming ( _⊆_ to _⊑_ )
open import Setoid.Congruences.Monolith             using  ( BelowDiagonal ; Nonzero )

private variable α ρ ℓ : Level
```
-->

#### The ambient group

Everything below is developed inside one parameterized module, so that the group, its
carrier, its curried operations, and the conjugation vocabulary are fixed once.

```agda
module GroupCongruences {α ρ : Level} (𝒢 : Group α ρ) where
  private
    𝑮 = proj₁ 𝒢
    G = 𝕌[ 𝑮 ]

  open Setoid 𝔻[ 𝑮 ]            using  ( _≈_ )
                                renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open SetoidReasoning 𝔻[ 𝑮 ]
  open Group-Op 𝒢               using  ( _∙_ ; ε ; _⁻¹ ; ∙-cong ; assoc-law
                                       ; idˡ-law ; idʳ-law ; invˡ-law ; invʳ-law )
  open GroupProperties ⟨ 𝒢 ⟩ᵍᵖ  using  ( ε⁻¹≈ε ; ⁻¹-involutive ; ⁻¹-anti-homo-∙
                                       ; \\-leftDividesʳ )
  open Conj 𝒢                   using  ( conj ; conj-ε ; IsNormal )
```

#### Four facts of group arithmetic

The correspondence rests on four small identities, each named so that no proof below
has to inline an equational chain about them.  The first two say that `x ∙ y ⁻¹ ≈ ε`
is *equivalent* to `x ≈ y` — this is what makes the relation `x ∙ y ⁻¹ ∈ N` collapse to
the setoid equality exactly when `N` is trivial.  The third is right-cancellation in the
form the round trip needs, and the fourth is the unit law that identifies `x ∙ ε ⁻¹`
with `x`.

```agda
  -- x ∙ y ⁻¹ ≈ ε implies x ≈ y (multiply on the right by y).
  ∙⁻¹≈ε→≈ : ∀ {x y} → x ∙ y ⁻¹ ≈ ε → x ≈ y
  ∙⁻¹≈ε→≈ {x} {y} h = begin
    x               ≈˘⟨ idʳ-law x ⟩
    x ∙ ε           ≈˘⟨ ∙-cong ≈refl (invˡ-law y) ⟩
    x ∙ (y ⁻¹ ∙ y)  ≈˘⟨ assoc-law x (y ⁻¹) y ⟩
    x ∙ y ⁻¹ ∙ y    ≈⟨ ∙-cong h ≈refl ⟩
    ε ∙ y           ≈⟨ idˡ-law y ⟩
    y               ∎

  -- ... and conversely, equal elements have trivial right quotient.
  ≈→∙⁻¹≈ε : ∀ {x y} → x ≈ y → x ∙ y ⁻¹ ≈ ε
  ≈→∙⁻¹≈ε {x} {y} x≈y = ≈trans (∙-cong x≈y ≈refl) (invʳ-law y)

  -- Right cancellation: the right quotient by y, multiplied back by y, is the identity.
  ∙⁻¹∙ : ∀ x y → x ∙ y ⁻¹ ∙ y ≈ x
  ∙⁻¹∙ x y = begin
    x ∙ y ⁻¹ ∙ y    ≈⟨ assoc-law x (y ⁻¹) y ⟩
    x ∙ (y ⁻¹ ∙ y)  ≈⟨ ∙-cong ≈refl (invˡ-law y) ⟩
    x ∙ ε           ≈⟨ idʳ-law x ⟩
    x               ∎

  -- The right quotient by the identity is the identity map.
  ∙ε⁻¹ : ∀ x → x ∙ ε ⁻¹ ≈ x
  ∙ε⁻¹ x = ≈trans (∙-cong ≈refl ε⁻¹≈ε) (idʳ-law x)
```

#### Normal subgroups as an ordered object

A **normal subgroup** of `𝒢`{.AgdaBound} at predicate level `ℓ`{.AgdaBound} is a
predicate on the carrier together with a proof that it is an equality-respecting
subgroup and a proof that it is closed under conjugation.  This is
`Subgroup`{.AgdaFunction} of [Classical.Structures.Group.Subgroups][] with
`IsNormal`{.AgdaFunction} of [Classical.Structures.Group.Conjugation][] adjoined; it is
introduced here rather than there because normality is the *only* extra datum the
correspondence needs, and no earlier module had cause to bundle it.

Normal subgroups are ordered by inclusion of the underlying predicates, with equality
mutual inclusion — the same shape as `_⊑_`{.AgdaFunction} and `_≑_`{.AgdaFunction} on
congruences, so that the isomorphism below can be stated without any bridging
construction on either side.

```agda
  -- A normal subgroup: an equality-respecting subgroup closed under conjugation.
  NormalSubgroup : (ℓ : Level) → Type (α ⊔ ρ ⊔ suc ℓ)
  NormalSubgroup ℓ = Σ[ N ∈ Pred G ℓ ] (IsSubgroup 𝒢 N × IsNormal N)

  -- The underlying predicate of a normal subgroup ...
  set : NormalSubgroup ℓ → Pred G ℓ
  set = proj₁

  -- ... and its two proof components.
  set-isSubgroup : (𝑵 : NormalSubgroup ℓ) → IsSubgroup 𝒢 (set 𝑵)
  set-isSubgroup 𝑵 = proj₁ (proj₂ 𝑵)

  set-normal : (𝑵 : NormalSubgroup ℓ) → IsNormal (set 𝑵)
  set-normal 𝑵 = proj₂ (proj₂ 𝑵)

  infix 4 _≤ⁿ_ _≈ⁿ_

  -- The inclusion order on normal subgroups ...
  _≤ⁿ_ : NormalSubgroup ℓ → NormalSubgroup ℓ → Type (α ⊔ ℓ)
  𝑴 ≤ⁿ 𝑵 = set 𝑴 ⊆ set 𝑵

  -- ... and the equivalence of mutual inclusion it is antisymmetric over.
  _≈ⁿ_ : NormalSubgroup ℓ → NormalSubgroup ℓ → Type (α ⊔ ℓ)
  𝑴 ≈ⁿ 𝑵 = 𝑴 ≤ⁿ 𝑵 × 𝑵 ≤ⁿ 𝑴
```

#### The relation attached to a subgroup

`NormalRel N`{.AgdaFunction} is the relation "`x` and `y` differ by an element of
`N`", written with the *right* quotient `x ∙ y ⁻¹`.  It is defined for an arbitrary
predicate, so that the hypotheses each of its properties needs can be stated exactly.

```agda
  -- x and y are related when their right quotient lies in N.
  NormalRel : Pred G ℓ → BinaryRel G ℓ
  NormalRel N x y = x ∙ y ⁻¹ ∈ N
```

For an equality-respecting subgroup `N`{.AgdaBound} — with no normality hypothesis —
`NormalRel N`{.AgdaFunction} is an equivalence relation that contains the setoid
equality.  Each clause is one closure property of `N`{.AgdaBound} transported along one
line of group arithmetic, exactly as in `Coset`{.AgdaModule} of
[Classical.Structures.Group.Cosets][] for the left-handed relation.

```agda
  module SubgroupRel {ℓ : Level} (N : Pred G ℓ) (N-sg : IsSubgroup 𝒢 N) where

    open IsSubgroup N-sg  using ( respects ; ∙-closed ; ε-closed ; ⁻¹-closed )

    infix 4 _∼_

    _∼_ : BinaryRel G ℓ
    _∼_ = NormalRel N

    -- Reflexivity is ε ∈ N transported along x ∙ x ⁻¹ ≈ ε.
    ∼-refl : ∀ {x} → x ∼ x
    ∼-refl {x} = respects (≈sym (invʳ-law x)) ε-closed

    -- Symmetry is closure under inverses, since (x ∙ y ⁻¹) ⁻¹ ≈ y ∙ x ⁻¹.
    ∼-sym : ∀ {x y} → x ∼ y → y ∼ x
    ∼-sym {x} {y} x∼y = respects inv-eq (⁻¹-closed x∼y)
      where
      inv-eq : (x ∙ y ⁻¹) ⁻¹ ≈ y ∙ x ⁻¹
      inv-eq = begin
        (x ∙ y ⁻¹) ⁻¹     ≈⟨ ⁻¹-anti-homo-∙ x (y ⁻¹) ⟩
        (y ⁻¹) ⁻¹ ∙ x ⁻¹  ≈⟨ ∙-cong (⁻¹-involutive y) ≈refl ⟩
        y ∙ x ⁻¹          ∎

    -- Transitivity is closure under products, since (x ∙ y ⁻¹) ∙ (y ∙ z ⁻¹) ≈ x ∙ z ⁻¹.
    ∼-trans : ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z
    ∼-trans {x} {y} {z} x∼y y∼z = respects prod-eq (∙-closed x∼y y∼z)
      where
      prod-eq : (x ∙ y ⁻¹) ∙ (y ∙ z ⁻¹) ≈ x ∙ z ⁻¹
      prod-eq = begin
        (x ∙ y ⁻¹) ∙ (y ∙ z ⁻¹)  ≈⟨ assoc-law x (y ⁻¹) (y ∙ z ⁻¹) ⟩
        x ∙ (y ⁻¹ ∙ (y ∙ z ⁻¹))  ≈⟨ ∙-cong ≈refl (\\-leftDividesʳ y (z ⁻¹)) ⟩
        x ∙ z ⁻¹                 ∎

    ∼-isEquivalence : IsEquivalence _∼_
    ∼-isEquivalence = record { refl = ∼-refl ; sym = ∼-sym ; trans = ∼-trans }

    -- The setoid equality refines the relation (this is the `reflexive` field a
    -- congruence must supply, and it is what makes the relation contain the diagonal).
    ≈⇒∼ : ∀ {x y} → x ≈ y → x ∼ y
    ≈⇒∼ x≈y = respects (≈sym (≈→∙⁻¹≈ε x≈y)) ε-closed

    -- Consequently the relation may be transported along ≈ in either argument.
    ∼-resp : ∀ {x x' y y'} → x ≈ x' → y ≈ y' → x ∼ y → x' ∼ y'
    ∼-resp x≈x' y≈y' p = ∼-trans (∼-trans (≈⇒∼ (≈sym x≈x')) p) (≈⇒∼ y≈y')
```

#### From a normal subgroup to a congruence

Adding normality makes the relation compatible with the three operations of
`Sig-Group`{.AgdaFunction}, hence a congruence.

Compatibility with `∙-Op`{.AgdaInductiveConstructor} is the substantive clause and the
only one that uses normality in an essential way: from `x ∙ y ⁻¹ ∈ N` and
`u ∙ v ⁻¹ ∈ N` we must produce `(x ∙ u) ∙ (y ∙ v) ⁻¹ ∈ N`, and the two given elements do
not multiply to it — one of them must first be *moved past* `x`{.AgdaBound}, which is
precisely conjugation.  Compatibility with `⁻¹-Op`{.AgdaInductiveConstructor} is one
conjugation as well; with `ε-Op`{.AgdaInductiveConstructor} it is reflexivity.

```agda
  module NormalCon {ℓ : Level} (𝑵 : NormalSubgroup ℓ) where

    private
      N : Pred G ℓ
      N = set 𝑵

    open IsSubgroup (set-isSubgroup 𝑵)  using ( respects ; ∙-closed )
    open SubgroupRel N (set-isSubgroup 𝑵) public

    normal : IsNormal N
    normal = set-normal 𝑵

    -- Compatibility with the curried multiplication.  The element x ∙ y ⁻¹ is on the
    -- wrong side of x ∙ u, so u ∙ v ⁻¹ is first conjugated by x — the one step that
    -- normality supplies and that fails for a non-normal subgroup.
    ∼-∙ : ∀ {x y u v} → x ∼ y → u ∼ v → (x ∙ u) ∼ (y ∙ v)
    ∼-∙ {x} {y} {u} {v} p q = respects step (∙-closed (normal x q) p)
      where
      step : x ∙ (u ∙ v ⁻¹) ∙ x ⁻¹ ∙ (x ∙ y ⁻¹) ≈ x ∙ u ∙ (y ∙ v) ⁻¹
      step = begin
        x ∙ (u ∙ v ⁻¹) ∙ x ⁻¹ ∙ (x ∙ y ⁻¹)    ≈⟨ assoc-law (x ∙ (u ∙ v ⁻¹)) (x ⁻¹) (x ∙ y ⁻¹) ⟩
        x ∙ (u ∙ v ⁻¹) ∙ (x ⁻¹ ∙ (x ∙ y ⁻¹))  ≈⟨ ∙-cong ≈refl (\\-leftDividesʳ x (y ⁻¹)) ⟩
        x ∙ (u ∙ v ⁻¹) ∙ y ⁻¹                 ≈˘⟨ ∙-cong (assoc-law x u (v ⁻¹)) ≈refl ⟩
        x ∙ u ∙ v ⁻¹ ∙ y ⁻¹                   ≈⟨ assoc-law (x ∙ u) (v ⁻¹) (y ⁻¹) ⟩
        x ∙ u ∙ (v ⁻¹ ∙ y ⁻¹)                 ≈˘⟨ ∙-cong ≈refl (⁻¹-anti-homo-∙ y v) ⟩
        x ∙ u ∙ (y ∙ v) ⁻¹                    ∎

    -- Compatibility with the curried inverse: conjugating x ∙ y ⁻¹ by x ⁻¹ produces
    -- y ⁻¹ ∙ (x ⁻¹) ⁻¹, which is the relation the other way round.
    ∼-⁻¹ : ∀ {x y} → x ∼ y → x ⁻¹ ∼ y ⁻¹
    ∼-⁻¹ {x} {y} p = ∼-sym (respects step (normal (x ⁻¹) p))
      where
      step : x ⁻¹ ∙ (x ∙ y ⁻¹) ∙ (x ⁻¹) ⁻¹ ≈ y ⁻¹ ∙ (x ⁻¹) ⁻¹
      step = ∙-cong (\\-leftDividesʳ x (y ⁻¹)) ≈refl

    -- Compatibility with every operation symbol.  Each clause is the corresponding
    -- curried fact, transported across the tuple-vs-curried interpretation bridges of
    -- [Classical.Structures.Group.Subgroups].
    ∼-compatible : 𝑮 ∣≈ _∼_
    ∼-compatible ∙-Op   {u} {v} p = ∼-resp  (≈sym (interp-tuple-∙ 𝒢 u))
                                            (≈sym (interp-tuple-∙ 𝒢 v))
                                            (∼-∙ (p 0F) (p 1F))
    ∼-compatible ε-Op   {u} {v} p = ∼-resp  (≈sym (interp-tuple-ε 𝒢 u))
                                            (≈sym (interp-tuple-ε 𝒢 v))
                                            ∼-refl
    ∼-compatible ⁻¹-Op  {u} {v} p = ∼-resp  (≈sym (interp-tuple-⁻¹ 𝒢 u))
                                            (≈sym (interp-tuple-⁻¹ 𝒢 v))
                                            (∼-⁻¹ (p 0F))

    -- The relation of a normal subgroup is a congruence of the group algebra.
    ∼-isCongruence : IsCongruence 𝑮 _∼_
    ∼-isCongruence = mkcon ≈⇒∼ ∼-isEquivalence ∼-compatible
```

For a normal subgroup the right-handed relation used here agrees with the left-handed
coset relation `Coset._∼_`{.AgdaFunction} of [Classical.Structures.Group.Cosets][],
which is the one [FLRP.Bridge][] builds on.  Both directions are one application of
`∼-⁻¹`{.AgdaFunction} followed by an involutivity rewrite, so nothing about the
development depends on which of the two presentations a consumer prefers.

```agda
    -- The right-coset relation of a normal subgroup is its left-coset relation ...
    rel→coset : ∀ {x y} → x ∼ y → Coset._∼_ 𝒢 N (set-isSubgroup 𝑵) x y
    rel→coset {x} {y} p = respects (∙-cong ≈refl (⁻¹-involutive y)) (∼-⁻¹ p)

    -- ... and conversely.
    coset→rel : ∀ {x y} → Coset._∼_ 𝒢 N (set-isSubgroup 𝑵) x y → x ∼ y
    coset→rel {x} {y} p = ∼-resp  (⁻¹-involutive x) (⁻¹-involutive y)
                                  (∼-⁻¹ (respects (∙-cong ≈refl (≈sym (⁻¹-involutive y))) p))
```

The forward map of the correspondence packages the relation with its congruence proof.

```agda
  -- N ↦ θ_N : a normal subgroup gives a congruence of the group algebra.
  congruenceOf : NormalSubgroup ℓ → Con 𝑮 ℓ
  congruenceOf 𝑵 = NormalRel (set 𝑵) , NormalCon.∼-isCongruence 𝑵
```

#### From a congruence to a normal subgroup

In the other direction the ingredients are the curried consequences of a congruence's
compatibility: it is preserved by multiplication, by inversion, and hence by
conjugation.  These are read off from `is-compatible`{.AgdaFunction} at the canonical
tuples, with no interpretation bridge needed — the curried accessors of
`Group-Op`{.AgdaModule} are *defined* by applying the interpreted symbol to exactly
those tuples.

```agda
  module ConNormal {ℓ : Level} (θ : Con 𝑮 ℓ) where

    infix 4 _≐_

    _≐_ : BinaryRel G ℓ
    _≐_ = proj₁ θ

    ≐-refl : ∀ {x} → x ≐ x
    ≐-refl = IsEquivalence.refl (is-equivalence (proj₂ θ))

    ≐-trans : ∀ {x y z} → x ≐ y → y ≐ z → x ≐ z
    ≐-trans = IsEquivalence.trans (is-equivalence (proj₂ θ))

    -- A congruence relates ≈-equal elements.
    ≐-reflexive : ∀ {x y} → x ≈ y → x ≐ y
    ≐-reflexive = reflexive (proj₂ θ)

    -- Compatibility with the curried multiplication ...
    ≐-∙ : ∀ {x y u v} → x ≐ y → u ≐ v → (x ∙ u) ≐ (y ∙ v)
    ≐-∙ {x} {y} {u} {v} p q =
      is-compatible (proj₂ θ) ∙-Op {pair x u} {pair y v} (λ { 0F → p ; 1F → q })

    -- ... and with the curried inverse.
    ≐-⁻¹ : ∀ {x y} → x ≐ y → x ⁻¹ ≐ y ⁻¹
    ≐-⁻¹ {x} {y} p = is-compatible (proj₂ θ) ⁻¹-Op {λ _ → x} {λ _ → y} (λ _ → p)

    -- Hence conjugation by any element preserves the congruence.
    ≐-conj : ∀ g {x y} → x ≐ y → conj g x ≐ conj g y
    ≐-conj g p = ≐-∙ (≐-∙ ≐-refl p) ≐-refl
```

The class of the identity is an equality-respecting subgroup, and it is normal.
Membership is `x θ ε`, so each subgroup law is one application of the corresponding
compatibility fact followed by a `≈`-step that renormalizes the right-hand side back to
`ε`{.AgdaFunction}: `ε ∙ ε ≈ ε`, `ε ⁻¹ ≈ ε`, and `conj g ε ≈ ε`.

```agda
    -- The θ-class of the identity.
    IdentityClass : Pred G ℓ
    IdentityClass x = x ≐ ε

    -- It respects the setoid equality, because a congruence contains it.
    IdentityClass-respects : IdentityClass Respects _≈_
    IdentityClass-respects x≈y p = ≐-trans (≐-reflexive (≈sym x≈y)) p

    IdentityClass-ε : ε ∈ IdentityClass
    IdentityClass-ε = ≐-refl

    IdentityClass-∙ : ∀ {x y} → x ∈ IdentityClass → y ∈ IdentityClass
      → x ∙ y ∈ IdentityClass
    IdentityClass-∙ p q = ≐-trans (≐-∙ p q) (≐-reflexive (idˡ-law ε))

    IdentityClass-⁻¹ : ∀ {x} → x ∈ IdentityClass → x ⁻¹ ∈ IdentityClass
    IdentityClass-⁻¹ p = ≐-trans (≐-⁻¹ p) (≐-reflexive ε⁻¹≈ε)

    -- The identity class is an equality-respecting subgroup ...
    IdentityClass-isSubgroup : IsSubgroup 𝒢 IdentityClass
    IdentityClass-isSubgroup = mkIsSubgroup 𝒢  IdentityClass-respects IdentityClass-∙
                                               IdentityClass-ε IdentityClass-⁻¹

    -- ... and it is normal, since conjugation fixes the identity.
    IdentityClass-normal : IsNormal IdentityClass
    IdentityClass-normal g p = ≐-trans (≐-conj g p) (≐-reflexive (conj-ε g))
```

The backward map of the correspondence packages the class with its two proofs.

```agda
  -- θ ↦ N_θ : a congruence gives a normal subgroup of the group.
  normalOf : Con 𝑮 ℓ → NormalSubgroup ℓ
  normalOf θ =  ConNormal.IdentityClass θ
             ,  ConNormal.IdentityClass-isSubgroup θ
             ,  ConNormal.IdentityClass-normal θ
```

#### Normality is necessary, not merely sufficient

`NormalCon`{.AgdaModule} shows normality *suffices* for `NormalRel N`{.AgdaFunction} to
be a congruence.  The converse holds too, and is worth proving rather than asserting:
were it left as prose, the claim "the correspondence is with the *normal* subgroups"
would be doing work the formal development had not done, and nothing would rule out the
relation of some non-normal subgroup slipping into `Con 𝑮 ℓ`{.AgdaFunction}.

The proof needs no new group arithmetic.  If `NormalRel N`{.AgdaFunction} is a
congruence, its identity class is normal by
`IdentityClass-normal`{.AgdaFunction} — and that class is
`{ x ∣ x ∙ ε ⁻¹ ∈ N }`, which `respects`{.AgdaField} identifies with
`N`{.AgdaBound} itself.

```agda
  -- If the relation of an equality-respecting subgroup is a congruence, the subgroup
  -- is normal.  With `NormalCon.∼-isCongruence` this makes normality *equivalent* to
  -- compatibility, so `NormalSubgroup ℓ` is exactly the source of the correspondence.
  congruence→normal : {ℓ : Level} (N : Pred G ℓ) → IsSubgroup 𝒢 N
    →  IsCongruence 𝑮 (NormalRel N) → IsNormal N
  congruence→normal N N-sg isCon g {x} x∈N =
    respects  (∙ε⁻¹ (conj g x))
              (ConNormal.IdentityClass-normal (NormalRel N , isCon) g
                (respects (≈sym (∙ε⁻¹ x)) x∈N))
    where open IsSubgroup N-sg using ( respects )
```

#### Monotonicity

Both maps act by (co)restriction of the underlying predicates and relations, so
monotonicity is immediate in each direction.

```agda
  -- The congruence-to-subgroup map is monotone.
  normalOf-mono : {θ φ : Con 𝑮 ℓ} → θ ⊑ φ → normalOf θ ≤ⁿ normalOf φ
  normalOf-mono θ⊑φ p = θ⊑φ p

  -- The subgroup-to-congruence map is monotone.
  congruenceOf-mono : {𝑴 𝑵 : NormalSubgroup ℓ} → 𝑴 ≤ⁿ 𝑵 → congruenceOf 𝑴 ⊑ congruenceOf 𝑵
  congruenceOf-mono 𝑴≤𝑵 p = 𝑴≤𝑵 p
```

`OrderIso`{.AgdaRecord} asks only for monotonicity, not for the maps to be well defined
on equivalence classes, so that latter property — which "isomorphism of posets" is
usually taken to include — is recorded here rather than left implicit.  It costs
nothing: each equivalence *is* mutual containment, so applying the matching
monotonicity twice suffices.

```agda
  -- Both maps respect the equivalences of the two sides.
  normalOf-cong : {θ φ : Con 𝑮 ℓ} → θ ≑ φ → normalOf θ ≈ⁿ normalOf φ
  normalOf-cong {ℓ} {θ} {φ} (θ⊑φ , φ⊑θ) =
    normalOf-mono {ℓ} {θ} {φ} θ⊑φ , normalOf-mono {ℓ} {φ} {θ} φ⊑θ

  congruenceOf-cong : {𝑴 𝑵 : NormalSubgroup ℓ}
    →  𝑴 ≈ⁿ 𝑵 → congruenceOf 𝑴 ≑ congruenceOf 𝑵
  congruenceOf-cong {ℓ} {𝑴} {𝑵} (𝑴≤𝑵 , 𝑵≤𝑴) =
    congruenceOf-mono {ℓ} {𝑴} {𝑵} 𝑴≤𝑵 , congruenceOf-mono {ℓ} {𝑵} {𝑴} 𝑵≤𝑴
```

#### Mutual inverseness

On congruences, `θ_{N_θ} ≑ θ`: the relation `θ_{N_θ}` holds at `(x , y)` when
`(x ∙ y ⁻¹) θ ε`, and multiplying on the right by `y`{.AgdaBound} converts that to
`x θ y` through `∙⁻¹∙`{.AgdaFunction} and the unit law — while multiplying `x θ y` on
the right by `y ⁻¹` converts it back through `invʳ-law`{.AgdaFunction}.

```agda
  -- Round trip on congruences: θ_{N_θ} ≑ θ.
  congruenceOf∘normalOf : (θ : Con 𝑮 ℓ) → congruenceOf (normalOf θ) ≑ θ
  congruenceOf∘normalOf θ = fwd , bwd
    where
    open ConNormal θ

    -- From (x ∙ y ⁻¹) θ ε derive x θ y.
    fwd : congruenceOf (normalOf θ) ⊑ θ
    fwd {x} {y} p = ≐-trans  (≐-reflexive (≈sym (∙⁻¹∙ x y)))
                             (≐-trans (≐-∙ p ≐-refl) (≐-reflexive (idˡ-law y)))

    -- From x θ y derive (x ∙ y ⁻¹) θ ε.
    bwd : θ ⊑ congruenceOf (normalOf θ)
    bwd {x} {y} p = ≐-trans (≐-∙ p (≐-refl {y ⁻¹})) (≐-reflexive (invʳ-law y))
```

On normal subgroups, `N_{θ_N} ≈ⁿ N`: an element `x`{.AgdaBound} lies in `N_{θ_N}` when
`x ∙ ε ⁻¹ ∈ N`, and `x ∙ ε ⁻¹ ≈ x`, so the `respects`{.AgdaField} proof carried by the
subgroup identifies the two.  **This is the step that consumes the
`respects`{.AgdaField} field**, and the sole place the correspondence would break for a
normal subuniverse not closed under the setoid equality.

```agda
  -- Round trip on normal subgroups: N_{θ_N} ≈ⁿ N (needs the respecting field).
  normalOf∘congruenceOf : (𝑵 : NormalSubgroup ℓ) → normalOf (congruenceOf 𝑵) ≈ⁿ 𝑵
  normalOf∘congruenceOf 𝑵 = fwd , bwd
    where
    open IsSubgroup (set-isSubgroup 𝑵) using ( respects )

    -- x ∙ ε ⁻¹ ∈ N and x ∙ ε ⁻¹ ≈ x give x ∈ N.
    fwd : normalOf (congruenceOf 𝑵) ≤ⁿ 𝑵
    fwd {x} p = respects (∙ε⁻¹ x) p

    -- x ∈ N and x ≈ x ∙ ε ⁻¹ give x ∙ ε ⁻¹ ∈ N.
    bwd : 𝑵 ≤ⁿ normalOf (congruenceOf 𝑵)
    bwd {x} p = respects (≈sym (∙ε⁻¹ x)) p
```

#### The order isomorphism

Assembling the four facts — two maps, both monotone, mutually inverse — gives the
correspondence as an `OrderIso`{.AgdaRecord} between the congruence containment order of
the group algebra and the inclusion order on normal subgroups.  (The endpoint implicits
of the monotone maps are bound and forwarded explicitly: `Con`{.AgdaFunction} and
`NormalSubgroup`{.AgdaFunction} are defined functions, not injective type formers, so
Agda cannot recover them from the field types.)

```agda
  -- The order isomorphism Con 𝑮 ℓ ≅ NormalSubgroup ℓ.
  NormalCongruenceIso : (ℓ : Level) → Type (α ⊔ ρ ⊔ suc ℓ)
  NormalCongruenceIso ℓ =
    OrderIso (_≑_ {𝑨 = 𝑮} {ℓ = ℓ}) (_⊑_ {𝑨 = 𝑮} {ℓ = ℓ}) (_≈ⁿ_ {ℓ}) (_≤ⁿ_ {ℓ})

  normal-congruence-iso : (ℓ : Level) → NormalCongruenceIso ℓ
  normal-congruence-iso ℓ = record
    { to         = normalOf
    ; from       = congruenceOf
    ; to-mono    = λ {θ} {φ} → normalOf-mono {ℓ} {θ} {φ}
    ; from-mono  = λ {𝑴} {𝑵} → congruenceOf-mono {ℓ} {𝑴} {𝑵}
    ; to∘from    = normalOf∘congruenceOf
    ; from∘to    = congruenceOf∘normalOf
    }
```

The reverse isomorphism presents the normal subgroups of `𝒢`{.AgdaBound} as the
congruence poset of its underlying algebra — the form a representability argument wants.

```agda
  NormalCongruenceIso⁻¹ : (ℓ : Level) → Type (α ⊔ ρ ⊔ suc ℓ)
  NormalCongruenceIso⁻¹ ℓ =
    OrderIso (_≈ⁿ_ {ℓ}) (_≤ⁿ_ {ℓ}) (_≑_ {𝑨 = 𝑮} {ℓ = ℓ}) (_⊑_ {𝑨 = 𝑮} {ℓ = ℓ})

  normal-congruence-iso⁻¹ : (ℓ : Level) → NormalCongruenceIso⁻¹ ℓ
  normal-congruence-iso⁻¹ ℓ = record
    { to         = congruenceOf
    ; from       = normalOf
    ; to-mono    = λ {𝑴} {𝑵} → congruenceOf-mono {ℓ} {𝑴} {𝑵}
    ; from-mono  = λ {θ} {φ} → normalOf-mono {ℓ} {θ} {φ}
    ; to∘from    = congruenceOf∘normalOf
    ; from∘to    = normalOf∘congruenceOf
    }
```

#### Nonzero congruences and nontrivial normal subgroups

The order isomorphism alone does not say that the two sides agree on which elements are
*above the bottom*; that has to be proved, and it is what the monolith transport will
consume.  The bottom of the subgroup side is `trivialSubgroup`{.AgdaFunction} of
[Classical.Structures.Group.Subgroups][] — the `≈`-class of the identity, which over a
setoid carrier is the right notion of the one-element subgroup — and the bottom of the
congruence side is the diagonal, whose "at the bottom" predicate is
`BelowDiagonal`{.AgdaFunction} of [Setoid.Congruences.Monolith][].

```agda
  -- N is contained in the trivial subgroup { x ∣ x ≈ ε }.
  BelowTrivial : Pred G ℓ → Type (α ⊔ ρ ⊔ ℓ)
  BelowTrivial N = N ⊆ proj₁ (trivialSubgroup 𝒢)

  -- N is nontrivial: it is not contained in the trivial subgroup.
  Nontrivialᴺ : Pred G ℓ → Type (α ⊔ ρ ⊔ ℓ)
  Nontrivialᴺ N = ¬ BelowTrivial N
```

The two positive statements are equivalent on each side, constructively and in both
directions; `Nonzero`{.AgdaFunction} and `Nontrivialᴺ`{.AgdaFunction} are their
negations, so the equivalence of the negations follows by contraposition with no
classical input.  We state the four positive implications first, since a downstream
proof usually wants one of them directly rather than the negated form.

```agda
  -- If N is trivial then θ_N relates only equal elements ...
  below-trivial→below-diagonal : (𝑵 : NormalSubgroup ℓ)
    →  BelowTrivial (set 𝑵) → BelowDiagonal 𝑮 (congruenceOf 𝑵)
  below-trivial→below-diagonal 𝑵 N⊆1 p = ∙⁻¹≈ε→≈ (N⊆1 p)

  -- ... and conversely, if θ_N relates only equal elements then N is trivial.
  below-diagonal→below-trivial : (𝑵 : NormalSubgroup ℓ)
    →  BelowDiagonal 𝑮 (congruenceOf 𝑵) → BelowTrivial (set 𝑵)
  below-diagonal→below-trivial 𝑵 θ⊆Δ {x} x∈N = θ⊆Δ (respects (≈sym (∙ε⁻¹ x)) x∈N)
    where open IsSubgroup (set-isSubgroup 𝑵) using ( respects )

  -- If θ relates only equal elements then its identity class is trivial ...
  con-below-diagonal→below-trivial : (θ : Con 𝑮 ℓ)
    →  BelowDiagonal 𝑮 θ → BelowTrivial (set (normalOf θ))
  con-below-diagonal→below-trivial θ θ⊆Δ x∈N = θ⊆Δ x∈N

  -- ... and conversely, a trivial identity class forces θ below the diagonal.
  con-below-trivial→below-diagonal : (θ : Con 𝑮 ℓ)
    →  BelowTrivial (set (normalOf θ)) → BelowDiagonal 𝑮 θ
  con-below-trivial→below-diagonal θ N⊆1 {x} {y} p =
    ∙⁻¹≈ε→≈ (N⊆1 (≐-trans (≐-∙ p (≐-refl {y ⁻¹})) (≐-reflexive (invʳ-law y))))
    where open ConNormal θ
```

Negating both sides gives the statement the monolith transport needs: under the
correspondence, a congruence is nonzero exactly when the matching normal subgroup is
nontrivial.

```agda
  -- θ_N is nonzero iff N is nontrivial.
  nonzero→nontrivial : (𝑵 : NormalSubgroup ℓ)
    →  Nonzero 𝑮 (congruenceOf 𝑵) → Nontrivialᴺ (set 𝑵)
  nonzero→nontrivial 𝑵 nz N⊆1 = nz (below-trivial→below-diagonal 𝑵 N⊆1)

  nontrivial→nonzero : (𝑵 : NormalSubgroup ℓ)
    →  Nontrivialᴺ (set 𝑵) → Nonzero 𝑮 (congruenceOf 𝑵)
  nontrivial→nonzero 𝑵 nt θ⊆Δ = nt (below-diagonal→below-trivial 𝑵 θ⊆Δ)

  -- N_θ is nontrivial iff θ is nonzero.
  con-nonzero→nontrivial : (θ : Con 𝑮 ℓ)
    →  Nonzero 𝑮 θ → Nontrivialᴺ (set (normalOf θ))
  con-nonzero→nontrivial θ nz N⊆1 = nz (con-below-trivial→below-diagonal θ N⊆1)

  con-nontrivial→nonzero : (θ : Con 𝑮 ℓ)
    →  Nontrivialᴺ (set (normalOf θ)) → Nonzero 𝑮 θ
  con-nontrivial→nonzero θ nt θ⊆Δ = nt (con-below-diagonal→below-trivial θ θ⊆Δ)
```
