---
layout: default
file: "src/FLRP/Enforceable.lagda.md"
title: "FLRP.Enforceable module (The Agda Universal Algebra Library)"
date: "2026-07-18"
author: "the agda-algebras development team"
---

### Interval enforceable properties of finite groups

This is the [FLRP.Enforceable][] module of the [Agda Universal Algebra Library][].

This module opens work package WP-4 of the FLRP research program: the formalization
of *interval enforceable* group properties, after the note *Interval enforceable
properties of finite groups* (arXiv:1205.1927, vendored at
`docs/papers/flrp/ieprops/`; see `docs/notes/flrp-research-roadmap.md` § 4).  A group
property `P` is **interval enforceable (IE) via a lattice `𝑳`** when every group
whose subgroup lattice has an upper interval isomorphic to `𝑳` must satisfy `P`;
it is **core-free interval enforceable (cf-IE)** when the same is only required of
representations over a *core-free* subgroup.  The note's program is to combine
enforceable properties into a contradiction, which by Pálfy–Pudlák would answer the
Finite Lattice Representation Problem negatively.

The contents, keyed to the note:

+  `GroupRepresentable`{.AgdaRecord} — the lattice occurs as an upper interval
   `[H , G]` in the subgroup lattice of a group, with all witnesses carried
   explicitly;
+  `IE`{.AgdaFunction}, `cfIE`{.AgdaFunction}, `minIE`{.AgdaFunction} — the note's
   § 2 definitions, with core-freeness expressed through WP-2's normal core;
+  the **fattening isomorphism** `[H × K , G × K] ≅ [H , G]`
   (`Fatten`{.AgdaModule}), in both coordinates;
+  **Lemma 3.2** (`lemma:ie-prop-and-neg`): a property and its negation cannot both
   be IE via group representable lattices (`no-contradictory-IE`{.AgdaFunction}),
   with the note's fattening remark as the companion
   `IE-fattens`{.AgdaFunction};
+  **Lemma 3.1** (`lemma-wjd-2`) and the parachute meta-theorem
   (`thm-wjd-1`) as *statements only*, their proofs deferred to RP-1 behind named
   hypothesis records in the `FLRP.Assumptions` style.

Two disciplines from the roadmap govern the definitions.

+  **Representability tracking (vacuity discipline)**.  If no group realizes `𝑳` as
   an upper interval then *every* property is vacuously enforceable via `𝑳`, and
   deciding that emptiness is the original problem.  So `IE`{.AgdaFunction} and
   `cfIE`{.AgdaFunction} are the bare universally quantified notions, and group
   representability of the enforcing lattice is a separate, explicitly tracked
   hypothesis (`GroupRepresentable`{.AgdaRecord}) that lemmas assume where the note
   assumes it — never silently quantified away.
+  **Levels**.  As in [FLRP.Problem][], groups are fixed at `Group 0ℓ 0ℓ` and
   subgroup predicates at level `0ℓ`: the records here quantify existentially over
   groups and predicates, and Agda cannot quantify existentially over universe
   levels, so the levels must be pinned; `0ℓ` suffices for every finite (indeed
   every set-sized) instance.  Group *properties* appear only in universally
   quantified positions, so they keep a polymorphic level `ℓP`.  Note that
   properties are *not* required to be isomorphism-invariant: the note's Lemma 3.2
   proof never uses invariance, and no definition below needs it.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.Enforceable where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                    using ( ⊥ )
open import Data.Fin.Base                 using ( Fin )
open import Data.Nat.Base                 using ( ℕ ; _+_ )
                                          renaming ( _≤_ to _≤ⁿ_ )
open import Data.Product                  using ( _,_ ; _×_ ; Σ-syntax ; proj₁ ; proj₂ )
open import Data.Unit.Base                using ( tt )
open import Level                         using ( Level ; 0ℓ ; _⊔_ ; Lift ; lift )
                                          renaming ( suc to lsuc )
open import Relation.Binary               using ( Setoid )
open import Relation.Binary.Definitions   using ( _Respects_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ )
open import Relation.Nullary              using ( ¬_ )
open import Relation.Unary                using ( Pred ; _∈_ ; _⊆_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice          using ( module Lattice-Order )
open import Classical.Small.Structures.Lattice    using ( Lattice )
open import Classical.Structures.Group.Basic      using ( Group )
open import Classical.Structures.Group.NormalCore using ( module Core )
open import Classical.Structures.Group.Product    using ( module GroupProduct
                                                        ; _×ᵍ_ ; _×ᶠ_ ; _ᶠ×_ )
open import Classical.Structures.Group.SubgroupLattice
                                                  using ( module GroupSublattice )
open import Classical.Structures.Group.Subgroups  using ( IsSubgroup ; trivialSubgroup )
open import FLRP.Problem                          using ( OrderIso ; FiniteLattice
                                                        ; toLattice )
open import Setoid.Algebras.Basic                 using ( 𝔻[_] ; 𝕌[_] )
open import Setoid.Algebras.Finite                using ( FiniteAlgebra )
open import Setoid.Homomorphisms.HomomorphicImages using ( _IsHomImageOf_ )
open import Setoid.Subalgebras.Subuniverses       using ( Subuniverses )
```
-->

#### Upper intervals of respecting subgroups

The group side of a representation is an upper interval `[H , G]` in the subgroup
lattice, presented through WP-2's machinery: `H` enters as a `Subᴸ`{.AgdaFunction}
element of the subuniverse lattice of [Setoid.Subalgebras.CompleteLattice][]
(packaged for groups by [Classical.Structures.Group.SubgroupLattice][]), and the
interval `[H , full]` is the `SubInterval`{.AgdaModule} instance of the generic
[Order.Interval][] construction.

One refinement is needed.  The elements of `SubInterval`{.AgdaModule} are *bare*
subuniverses, with no compatibility between the predicate and the setoid equality of
the carrier.  Over a setoid-presented group that is too permissive: a subgroup is a
sub*set* of the carrier, i.e. an `≈`-saturated predicate, and bare subuniverses can
distinguish `≈`-equal elements.  The distinction is not cosmetic — over a carrier
with a redundant representative the bare interval `[H × K , G × K]` can be strictly
larger than `[H , G]`, so the fattening isomorphism below is *false* at the bare
level.[^1]  We therefore take as interval elements the bare interval elements
*paired with a proof that the predicate respects `≈`* — exactly the
`respects`{.AgdaField} field of `IsSubgroup`{.AgdaRecord}.  Over a group presented
on a propositional-equality setoid (the `eqsToGroup`{.AgdaFunction} builders, and
every finite Cayley-table group) the extra field is inhabited by `subst`, so nothing
is lost in the concrete cases the FLRP cares about.

`UpperInterval 𝒢 H H-sg`{.AgdaModule} packages the respecting upper interval
`[H , full]` for a fixed subgroup: the carrier `Interval≈`{.AgdaFunction}, its
equality and order (those of the bare interval, which ignore all proof components),
accessors, and the smart constructor `mk`{.AgdaFunction}.

```agda
module UpperInterval
  (𝒢 : Group 0ℓ 0ℓ) (H : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ) (H-sg : IsSubgroup 𝒢 H)
  where

  open Setoid 𝔻[ proj₁ 𝒢 ] using ( _≈_ )
  open GroupSublattice 𝒢 0ℓ using ( Subᴸ ; 1ˢ ; 1ˢ-maximum ; subgroup→Subᴸ
                                  ; module SubInterval )

  -- The bottom of the interval: H as an element of the subuniverse lattice.
  H↑ : Subᴸ
  H↑ = subgroup→Subᴸ H H-sg

  -- The bare interval [H , full], by the generic construction.
  module Bare = SubInterval H↑ 1ˢ (1ˢ-maximum H↑)

  -- An interval element: a bare element whose predicate respects ≈.
  Interval≈ : Type (lsuc 0ℓ)
  Interval≈ = Σ[ M ∈ Bare.Interval ] (proj₁ (proj₁ M) Respects _≈_)

  -- Accessors: the underlying predicate and its three certificates.
  pred : Interval≈ → Pred 𝕌[ proj₁ 𝒢 ] 0ℓ
  pred M = proj₁ (proj₁ (proj₁ M))

  pred-isSubuniverse : (M : Interval≈) → pred M ∈ Subuniverses (proj₁ 𝒢)
  pred-isSubuniverse M = proj₂ (proj₁ (proj₁ M))

  pred-respects : (M : Interval≈) → pred M Respects _≈_
  pred-respects M = proj₂ M

  above : (M : Interval≈) → H ⊆ pred M
  above M = proj₁ (proj₂ (proj₁ M))

  -- An interval element is a respecting subgroup.
  element-isSubgroup : (M : Interval≈) → IsSubgroup 𝒢 (pred M)
  element-isSubgroup M = record  { respects       = pred-respects M
                                 ; isSubuniverse  = pred-isSubuniverse M }

  -- Conversely, a respecting subgroup above H is an interval element
  -- (the top bound against the full subuniverse is trivial).
  mk : (M : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ) → IsSubgroup 𝒢 M → H ⊆ M → Interval≈
  mk M M-sg H⊆M =
    ((M , IsSubgroup.isSubuniverse M-sg) , H⊆M , (λ _ → lift tt))
    , IsSubgroup.respects M-sg

  -- Equality and order come from the bare interval (they compare the
  -- underlying predicates and ignore the respects proof).
  infix 4 _≈ᵢ_ _≤ᵢ_

  _≈ᵢ_ : Interval≈ → Interval≈ → Type 0ℓ
  M ≈ᵢ N = Bare._≈_ (proj₁ M) (proj₁ N)

  _≤ᵢ_ : Interval≈ → Interval≈ → Type 0ℓ
  M ≤ᵢ N = Bare._≤_ (proj₁ M) (proj₁ N)
```

#### Interval isomorphism with a classical lattice

`IntervalIso 𝒢 H H-sg 𝑳`{.AgdaFunction} is the group-side analog of
`ConIso`{.AgdaFunction} of [FLRP.Problem][], and deliberately the *same
presentation*: an `OrderIso`{.AgdaRecord} between the respecting upper interval
`[H , full]` of `Sub(𝒢)` and the meet order of the classical lattice
`𝑳`{.AgdaBound} of [Classical.Small.Structures.Lattice][].  Order isomorphisms
transport meets and joins, so this is exactly "`[H , G] ≅ 𝑳` as lattices" with no
redundant clauses.  (`OrderIso`{.AgdaRecord} still lives in [FLRP.Problem][]; its
planned migration to the `Order/` tree, foreseen there, is left to a dedicated
change.)

```agda
IntervalIso :
  (𝒢 : Group 0ℓ 0ℓ) (H : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ) (H-sg : IsSubgroup 𝒢 H)
  → Lattice → Type (lsuc 0ℓ)
IntervalIso 𝒢 H H-sg 𝑳 =
  OrderIso  (UpperInterval._≈ᵢ_ 𝒢 H H-sg) (UpperInterval._≤ᵢ_ 𝒢 H H-sg)
            (Setoid._≈_ 𝔻[ proj₁ 𝑳 ]) (Lattice-Order._≤_ 𝑳)
```

Interval isomorphisms compose with order isomorphisms *between* two intervals: the
mutually-inverse maps compose, and the round trips are repaired using that interval
equality is mutual inclusion (so it maps into the target through monotonicity and
the meet order's antisymmetry).  This small combinator is the engine of the
fattening applications below.

```agda
compose-IntervalIso :
  (𝒬 : Group 0ℓ 0ℓ) (J : Pred 𝕌[ proj₁ 𝒬 ] 0ℓ) (J-sg : IsSubgroup 𝒬 J)
  (ℛ : Group 0ℓ 0ℓ) (B : Pred 𝕌[ proj₁ ℛ ] 0ℓ) (B-sg : IsSubgroup ℛ B)
  (𝑳 : Lattice)
  → OrderIso  (UpperInterval._≈ᵢ_ 𝒬 J J-sg) (UpperInterval._≤ᵢ_ 𝒬 J J-sg)
              (UpperInterval._≈ᵢ_ ℛ B B-sg) (UpperInterval._≤ᵢ_ ℛ B B-sg)
  → IntervalIso ℛ B B-sg 𝑳
  → IntervalIso 𝒬 J J-sg 𝑳
compose-IntervalIso 𝒬 J J-sg ℛ B B-sg 𝑳 F Iso = record
  { to         = λ x → I2.to (F'.to x)
  ; from       = λ u → F'.from (I2.from u)
  ; to-mono    = λ le → I2.to-mono (F'.to-mono le)
  ; from-mono  = λ le → F'.from-mono (I2.from-mono le)
  ; to∘from    = λ u → ≈ᴸ-trans
      (≤ᴸ-antisym  (I2.to-mono (proj₁ (F'.to∘from (I2.from u))))
                   (I2.to-mono (proj₂ (F'.to∘from (I2.from u)))))
      (I2.to∘from u)
  ; from∘to    = λ x →
      ( (λ z → proj₁ (F'.from∘to x) (F'.from-mono (proj₁ (I2.from∘to (F'.to x))) z))
      , (λ z → F'.from-mono (proj₂ (I2.from∘to (F'.to x))) (proj₂ (F'.from∘to x) z)) )
  }
  where
  module F' = OrderIso F
  module I2 = OrderIso Iso
  open Lattice-Order 𝑳 using () renaming ( ≤-antisym to ≤ᴸ-antisym )
  open Setoid 𝔻[ proj₁ 𝑳 ] using () renaming ( trans to ≈ᴸ-trans )
```

#### Group representability

A lattice is **group representable** when it occurs as an upper interval in the
subgroup lattice of a group.  Per the vacuity discipline, this is a first-class
record whose fields carry all witnesses — the group, the subgroup predicate, its
subgroup proof, and the interval isomorphism — mirroring
`Representable`{.AgdaRecord} of [FLRP.Problem][] on the algebra side.  (The note
works with *finite* groups throughout; finiteness of the witness is deliberately not
baked in here, since none of the lemmas of this module consume it — it will enter
through `FiniteAlgebra`{.AgdaRecord} hypotheses exactly where a result needs it, as
`minIE`{.AgdaFunction} already illustrates.)

```agda
record GroupRepresentable (𝑳 : Lattice) : Type (lsuc 0ℓ) where
  field
    grp           : Group 0ℓ 0ℓ
    sub           : Pred 𝕌[ proj₁ grp ] 0ℓ
    isSubgroup    : IsSubgroup grp sub
    interval-iso  : IntervalIso grp sub isSubgroup 𝑳
```

#### Group properties and the enforceability classification

A *group property* here is any predicate on groups (at a polymorphic level, per the
level discipline above; isomorphism-invariance is not required, and none of the
results below use it).

```agda
GroupProperty : (ℓP : Level) → Type (lsuc 0ℓ ⊔ lsuc ℓP)
GroupProperty ℓP = Pred (Group 0ℓ 0ℓ) ℓP
```

`IE P 𝑳` is the note's display: every group with an upper interval isomorphic to
`𝑳` has property `P`.

```agda
IE : {ℓP : Level} → GroupProperty ℓP → Lattice → Type (lsuc 0ℓ ⊔ ℓP)
IE P 𝑳 =
  ∀ (𝒢 : Group 0ℓ 0ℓ) (H : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ) (H-sg : IsSubgroup 𝒢 H)
  → IntervalIso 𝒢 H H-sg 𝑳
  → P 𝒢
```

Core-freeness of a subgroup is expressed through WP-2's normal core: the core of
`H` — the greatest normal subgroup below `H`, constructed in
[Classical.Structures.Group.NormalCore][] as the meet of all conjugates — is
contained in the trivial subgroup (the `≈`-class of the identity).  The converse
containment always holds (the core is a subgroup, hence contains the identity's
class), so this inclusion says exactly "the core *is* trivial".

```agda
CoreFree :
  (𝒢 : Group 0ℓ 0ℓ) (H : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ) → IsSubgroup 𝒢 H → Type 0ℓ
CoreFree 𝒢 H H-sg = proj₁ (Core.core 𝒢 H H-sg) ⊆ proj₁ (trivialSubgroup 𝒢)
```

`cfIE P 𝑳` weakens `IE` by demanding the conclusion only for representations over a
core-free subgroup; consequently every IE property is cf-IE (the note's "clearly").

```agda
cfIE : {ℓP : Level} → GroupProperty ℓP → Lattice → Type (lsuc 0ℓ ⊔ ℓP)
cfIE P 𝑳 =
  ∀ (𝒢 : Group 0ℓ 0ℓ) (H : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ) (H-sg : IsSubgroup 𝒢 H)
  → CoreFree 𝒢 H H-sg
  → IntervalIso 𝒢 H H-sg 𝑳
  → P 𝒢

-- Interval enforceable implies core-free interval enforceable.
IE→cfIE : {ℓP : Level} {P : GroupProperty ℓP} {𝑳 : Lattice} → IE P 𝑳 → cfIE P 𝑳
IE→cfIE ie 𝒢 H H-sg _ iso = ie 𝒢 H H-sg iso
```

`minIE P 𝑳` asks for `P` only of *minimal* representations.  Minimality is measured
through the `card`{.AgdaField} field of the `FiniteAlgebra`{.AgdaRecord} interface
on the group's underlying algebra: the given representation's certified cardinality
is at most that of every other finite representation of `𝑳`.  Since
`card`{.AgdaField} bounds the carrier from above (the enumeration is surjective, not
bijective), this is minimality of *certified* cardinalities; with exact enumerations
it is the note's `|G|`-minimality.  The note has little to say about min-IE and
neither do we — the definition is recorded because such properties arise in the
literature (Lucchini's intervals, Pálfy's analysis of Feit's examples) and the
catalog of RP-2 will want to state them.

```agda
minIE : {ℓP : Level} → GroupProperty ℓP → Lattice → Type (lsuc 0ℓ ⊔ ℓP)
minIE P 𝑳 =
  ∀ (𝒢 : Group 0ℓ 0ℓ) (H : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ) (H-sg : IsSubgroup 𝒢 H)
    (fin : FiniteAlgebra (proj₁ 𝒢))
  → IntervalIso 𝒢 H H-sg 𝑳
  → ( ∀ (𝒬 : Group 0ℓ 0ℓ) (J : Pred 𝕌[ proj₁ 𝒬 ] 0ℓ) (J-sg : IsSubgroup 𝒬 J)
        (fin' : FiniteAlgebra (proj₁ 𝒬))
      → IntervalIso 𝒬 J J-sg 𝑳
      → FiniteAlgebra.card fin ≤ⁿ FiniteAlgebra.card fin' )
  → P 𝒢
```

#### The fattening isomorphism

The heart of this slice: for a subgroup `H` of `𝒢` and any group `𝒦`, the upper
interval over the fattened subgroup `H ×ᶠ 𝒦` in `Sub(𝒢 ×ᵍ 𝒦)` is order-isomorphic
to the upper interval over `H` in `Sub(𝒢)` — the note's `[H × K , G × K] ≅ [H , G]`.
The two maps are restriction to the first coordinate, `M ↦ (λ g → M (g , ε))`, and
pullback along the projection, `A ↦ (A ∘ proj₁)`; that they are well-defined,
monotone, and mutually inverse is the content of the `Slice₁`{.AgdaModule} toolkit
of [Classical.Structures.Group.Product][] — the pivot being that a respecting
subgroup `M ⊇ H ×ᶠ 𝒦` satisfies `M (g , k) ⟺ M (g , ε)`, since
`(g , k) ≈ (g , ε) ∙ (ε , k)` and `(ε , k)` lies in `H ×ᶠ 𝒦 ⊆ M`.  One round trip
is even definitional: restricting a pulled-back subgroup gives back exactly the
predicate one started from.

`FattenSnd`{.AgdaModule} fattens by a full *second* factor (the note's displayed
form); `FattenFst`{.AgdaModule} is the mirror with a full *first* factor.  Lemma 3.2
needs both, one per witness.

```agda
module Fatten (𝒢 𝒦 : Group 0ℓ 0ℓ) where

  private
    𝒫 : Group 0ℓ 0ℓ
    𝒫 = 𝒢 ×ᵍ 𝒦

  open GroupProduct 𝒢 𝒦 using ( module Slice₁ ; module Slice₂
                              ; ×ᶠ-isSubgroup ; ᶠ×-isSubgroup )

  module FattenSnd (H : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ) (H-sg : IsSubgroup 𝒢 H) where

    -- The fattened subgroup of the product.
    HP-sg : IsSubgroup 𝒫 (H ×ᶠ 𝒦)
    HP-sg = ×ᶠ-isSubgroup H-sg

    module IG = UpperInterval 𝒢 H H-sg
    module IP = UpperInterval 𝒫 (H ×ᶠ 𝒦) HP-sg

    -- Restriction: an interval element over H ×ᶠ 𝒦 restricts to one over H.
    to-fatten : IP.Interval≈ → IG.Interval≈
    to-fatten M = IG.mk S.restrict₁ S.restrict₁-isSubgroup S.restrict₁-⊇H
      where
      module S = Slice₁ H H-sg (IP.pred M) (IP.pred-isSubuniverse M)
                        (IP.pred-respects M) (IP.above M)

    -- Pullback: an interval element over H fattens to one over H ×ᶠ 𝒦.
    from-fatten : IG.Interval≈ → IP.Interval≈
    from-fatten A = IP.mk  (IG.pred A ×ᶠ 𝒦)
                           (×ᶠ-isSubgroup (IG.element-isSubgroup A))
                           (λ h → IG.above A h)

    -- Both maps are monotone (they act by composition on the predicates).
    to-fatten-mono : (M N : IP.Interval≈)
      → IP._≤ᵢ_ M N → IG._≤ᵢ_ (to-fatten M) (to-fatten N)
    to-fatten-mono M N M⊆N m = M⊆N m

    from-fatten-mono : (A A' : IG.Interval≈)
      → IG._≤ᵢ_ A A' → IP._≤ᵢ_ (from-fatten A) (from-fatten A')
    from-fatten-mono A A' A⊆A' a = A⊆A' a

    -- Restricting a pullback is the identity, definitionally.
    to∘from-fatten : (A : IG.Interval≈) → IG._≈ᵢ_ (to-fatten (from-fatten A)) A
    to∘from-fatten A = (λ z → z) , (λ z → z)

    -- Pulling back a restriction recovers M, by the slice pivot.
    from∘to-fatten : (M : IP.Interval≈) → IP._≈ᵢ_ (from-fatten (to-fatten M)) M
    from∘to-fatten M = (λ z → S.slice-in z) , (λ z → S.slice-out z)
      where
      module S = Slice₁ H H-sg (IP.pred M) (IP.pred-isSubuniverse M)
                        (IP.pred-respects M) (IP.above M)

    -- The fattening isomorphism  [H ×ᶠ 𝒦 , full] ≅ [H , full].
    -- (In from-mono the inclusion's element p is passed explicitly: the
    -- fattened predicates factor through proj₁, so an implicit p would leave
    -- its second component an unconstrained metavariable.)
    fatten-iso : OrderIso IP._≈ᵢ_ IP._≤ᵢ_ IG._≈ᵢ_ IG._≤ᵢ_
    fatten-iso = record
      { to         = to-fatten
      ; from       = from-fatten
      ; to-mono    = λ {M} {N} le → to-fatten-mono M N le
      ; from-mono  = λ {A} {A'} le {p} a → from-fatten-mono A A' le {p} a
      ; to∘from    = to∘from-fatten
      ; from∘to    = from∘to-fatten
      }

    -- Consequently any interval isomorphism [H , G] ≅ 𝑳 fattens to the product.
    fatten-IntervalIso : (𝑳 : Lattice)
      → IntervalIso 𝒢 H H-sg 𝑳 → IntervalIso 𝒫 (H ×ᶠ 𝒦) HP-sg 𝑳
    fatten-IntervalIso 𝑳 iso =
      compose-IntervalIso 𝒫 (H ×ᶠ 𝒦) HP-sg 𝒢 H H-sg 𝑳 fatten-iso iso

  module FattenFst (J : Pred 𝕌[ proj₁ 𝒦 ] 0ℓ) (J-sg : IsSubgroup 𝒦 J) where

    -- The mirrored fattened subgroup of the product.
    JP-sg : IsSubgroup 𝒫 (𝒢 ᶠ× J)
    JP-sg = ᶠ×-isSubgroup J-sg

    module IK = UpperInterval 𝒦 J J-sg
    module IP = UpperInterval 𝒫 (𝒢 ᶠ× J) JP-sg

    -- Restriction to the second coordinate.
    to-fatten : IP.Interval≈ → IK.Interval≈
    to-fatten M = IK.mk S.restrict₂ S.restrict₂-isSubgroup S.restrict₂-⊇J
      where
      module S = Slice₂ J J-sg (IP.pred M) (IP.pred-isSubuniverse M)
                        (IP.pred-respects M) (IP.above M)

    -- Pullback along the second projection.
    from-fatten : IK.Interval≈ → IP.Interval≈
    from-fatten A = IP.mk  (𝒢 ᶠ× IK.pred A)
                           (ᶠ×-isSubgroup (IK.element-isSubgroup A))
                           (λ j → IK.above A j)

    to-fatten-mono : (M N : IP.Interval≈)
      → IP._≤ᵢ_ M N → IK._≤ᵢ_ (to-fatten M) (to-fatten N)
    to-fatten-mono M N M⊆N m = M⊆N m

    from-fatten-mono : (A A' : IK.Interval≈)
      → IK._≤ᵢ_ A A' → IP._≤ᵢ_ (from-fatten A) (from-fatten A')
    from-fatten-mono A A' A⊆A' a = A⊆A' a

    to∘from-fatten : (A : IK.Interval≈) → IK._≈ᵢ_ (to-fatten (from-fatten A)) A
    to∘from-fatten A = (λ z → z) , (λ z → z)

    from∘to-fatten : (M : IP.Interval≈) → IP._≈ᵢ_ (from-fatten (to-fatten M)) M
    from∘to-fatten M = (λ z → S.slice-in z) , (λ z → S.slice-out z)
      where
      module S = Slice₂ J J-sg (IP.pred M) (IP.pred-isSubuniverse M)
                        (IP.pred-respects M) (IP.above M)

    -- The mirrored fattening isomorphism  [𝒢 ᶠ× J , full] ≅ [J , full].
    -- (Same explicit-p idiom as in FattenSnd, now factoring through proj₂.)
    fatten-iso : OrderIso IP._≈ᵢ_ IP._≤ᵢ_ IK._≈ᵢ_ IK._≤ᵢ_
    fatten-iso = record
      { to         = to-fatten
      ; from       = from-fatten
      ; to-mono    = λ {M} {N} le → to-fatten-mono M N le
      ; from-mono  = λ {A} {A'} le {p} a → from-fatten-mono A A' le {p} a
      ; to∘from    = to∘from-fatten
      ; from∘to    = from∘to-fatten
      }

    fatten-IntervalIso : (𝑳 : Lattice)
      → IntervalIso 𝒦 J J-sg 𝑳 → IntervalIso 𝒫 (𝒢 ᶠ× J) JP-sg 𝑳
    fatten-IntervalIso 𝑳 iso =
      compose-IntervalIso 𝒫 (𝒢 ᶠ× J) JP-sg 𝒦 J J-sg 𝑳 fatten-iso iso
```

#### Lemma 3.2: no property and its negation are both IE via representable lattices

The note's Lemma `lemma:ie-prop-and-neg`, in its two-line form: if `P` is IE via a
group representable `𝑳₁` and `¬ P` is IE via a group representable `𝑳₂`, take the
witnesses `[H₁ , G₁] ≅ 𝑳₁` and `[H₂ , G₂] ≅ 𝑳₂` and consider `G₁ × G₂`.  Fattening
gives `𝑳₁ ≅ [H₁ × G₂ , G₁ × G₂]` and `𝑳₂ ≅ [G₁ × H₂ , G₁ × G₂]`, so the two
enforceability assumptions make `G₁ × G₂` satisfy `P` and `¬ P` simultaneously.
Note where representability enters: without the two witnesses there is no product
group to build, which is precisely why the vacuity discipline refuses to quantify
representability away.

```agda
no-contradictory-IE :
  {ℓP : Level} (P : GroupProperty ℓP) (𝑳₁ 𝑳₂ : Lattice)
  → GroupRepresentable 𝑳₁ → IE P 𝑳₁
  → GroupRepresentable 𝑳₂ → IE (λ 𝒢 → ¬ P 𝒢) 𝑳₂
  → ⊥
no-contradictory-IE P 𝑳₁ 𝑳₂ rep₁ ie₁ rep₂ ie₂ = ¬P× P×
  where
  open GroupRepresentable rep₁
    renaming ( grp to 𝒢₁ ; sub to H₁ ; isSubgroup to H₁-sg ; interval-iso to iso₁ )
  open GroupRepresentable rep₂
    renaming ( grp to 𝒢₂ ; sub to H₂ ; isSubgroup to H₂-sg ; interval-iso to iso₂ )

  module F₂ = Fatten.FattenSnd 𝒢₁ 𝒢₂ H₁ H₁-sg
  module F₁ = Fatten.FattenFst 𝒢₁ 𝒢₂ H₂ H₂-sg

  P× : P (𝒢₁ ×ᵍ 𝒢₂)
  P× = ie₁ (𝒢₁ ×ᵍ 𝒢₂) (H₁ ×ᶠ 𝒢₂) F₂.HP-sg (F₂.fatten-IntervalIso 𝑳₁ iso₁)

  ¬P× : ¬ P (𝒢₁ ×ᵍ 𝒢₂)
  ¬P× = ie₂ (𝒢₁ ×ᵍ 𝒢₂) (𝒢₁ ᶠ× H₂) F₁.JP-sg (F₁.fatten-IntervalIso 𝑳₂ iso₂)
```

The fattening remark that follows the lemma in the note: if `P` is IE via a group
representable lattice, then `P` holds of the witness's product with *every* group —
so no property that a direct factor can destroy (solvability, being alternating or
symmetric, …) is IE via a representable lattice.

```agda
IE-fattens :
  {ℓP : Level} (P : GroupProperty ℓP) (𝑳 : Lattice)
  → IE P 𝑳 → (r : GroupRepresentable 𝑳)
  → (𝒦 : Group 0ℓ 0ℓ) → P (GroupRepresentable.grp r ×ᵍ 𝒦)
IE-fattens P 𝑳 ie r 𝒦 =
  ie (grp ×ᵍ 𝒦) (sub ×ᶠ 𝒦) F.HP-sg (F.fatten-IntervalIso 𝑳 interval-iso)
  where
  open GroupRepresentable r
  module F = Fatten.FattenSnd grp 𝒦 sub isSubgroup
```

Both arguments place the fattened subgroup *inside* a nontrivial normal subgroup of
the product (`1 × K` lies in the core of `H × K`), so fattening destroys
core-freeness and neither result transfers to the cf-IE level.  This is precisely
why the note's program — and RP-3's hunt for contradictory families — lives at the
core-free level, where an analog of Lemma 3.2 is not a theorem but the open
dead-end question of RP-4.

#### Lemma 3.1, stated with named hypotheses

The note's Lemma `lemma-wjd-2` upgrades cf-IE to IE when the complementary class is
closed under homomorphic images.  Its proof needs the **core-free reduction**: for
`N = Core_G(H)` one has `[H , G] ≅ [H/N , G/N]` with `H/N` core-free in `G/N`, and
`G/N` a homomorphic image of `G`.  Quotient groups are not yet in the library, so —
per the `FLRP.Assumptions` discipline of the roadmap (§ 6): formal statements even
for results whose proofs stay on paper, hypotheses as named records — the reduction
enters as the hypothesis record `CoreFreeReduction`{.AgdaRecord}, and Lemma 3.1 is
*stated* conditionally on it, its proof deferred to RP-1.

```agda
record CoreFreeReduction : Type (lsuc 0ℓ) where
  field
    reduce :
      (𝒢 : Group 0ℓ 0ℓ) (H : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ) (H-sg : IsSubgroup 𝒢 H)
      → Σ[ 𝒬 ∈ Group 0ℓ 0ℓ ]
        Σ[ J ∈ Pred 𝕌[ proj₁ 𝒬 ] 0ℓ ]
        Σ[ J-sg ∈ IsSubgroup 𝒬 J ]
          ( CoreFree 𝒬 J J-sg
          × ((𝑳 : Lattice) → IntervalIso 𝒢 H H-sg 𝑳 → IntervalIso 𝒬 J J-sg 𝑳)
          × ((proj₁ 𝒬) IsHomImageOf (proj₁ 𝒢)) )
```

The lemma's other hypothesis, H-closure of the complementary class: homomorphic
images of groups without `P` are without `P`.  (A homomorphism of the underlying
`Sig-Group` algebras is automatically a group homomorphism, so
`_IsHomImageOf_`{.AgdaFunction} of [Setoid.Homomorphisms.HomomorphicImages][] is the
right notion.)

```agda
ComplementHClosed : {ℓP : Level} → GroupProperty ℓP → Type (lsuc 0ℓ ⊔ ℓP)
ComplementHClosed P =
  ∀ (𝒢 𝒬 : Group 0ℓ 0ℓ) → (proj₁ 𝒬) IsHomImageOf (proj₁ 𝒢) → ¬ P 𝒢 → ¬ P 𝒬
```

One constructive gloss.  The note's argument is by contradiction: from a
representation `[H , G] ≅ 𝑳`, reduce to the core-free `[H/N , G/N] ≅ 𝑳`, conclude
`P (G/N)` by cf-IE, and note that `¬ P G` would propagate to `¬ P (G/N)` by
H-closure — so the argument constructively establishes `¬ ¬ P G`, and reaching
`P G` itself needs `P` stable under double negation.  We record stability as a
third named hypothesis rather than silently classicizing; RP-1 will prove the
`¬ ¬`-free variant outright and this one under stability.

```agda
PropertyStable : {ℓP : Level} → GroupProperty ℓP → Type (lsuc 0ℓ ⊔ ℓP)
PropertyStable P = ∀ (𝒢 : Group 0ℓ 0ℓ) → ¬ ¬ P 𝒢 → P 𝒢

-- Lemma 3.1 (lemma-wjd-2 of the note), as a statement: the type is defined,
-- no inhabitant is claimed here; the proof is RP-1's first target.
cfIE→IE-Statement : {ℓP : Level} → GroupProperty ℓP → Type (lsuc 0ℓ ⊔ ℓP)
cfIE→IE-Statement P =
    CoreFreeReduction
  → ComplementHClosed P
  → PropertyStable P
  → (𝑳 : Lattice) → cfIE P 𝑳 → IE P 𝑳
```

#### The parachute meta-theorem, stated with named hypotheses

Statement (B) of Pálfy–Pudlák, on the group side: every finite lattice is group
representable.  This is the exact analog of `FLRP-Statement`{.AgdaFunction} of
[FLRP.Problem][] — a type the library states but does not assert.

```agda
GroupFLRP-Statement : Type (lsuc 0ℓ)
GroupFLRP-Statement = (𝑳 : FiniteLattice) → GroupRepresentable (toLattice 𝑳)
```

Theorem `thm-wjd-1` of the note proves (B) equivalent to a statement (C) about
finite families of cf-IE classes.  Its hypotheses need two side conditions made
formal: a lattice *has more than two elements* (three pairwise `≈`-distinct
elements exist), and *at least two members* of the family do.

```agda
HasThreeDistinct : Lattice → Type 0ℓ
HasThreeDistinct 𝑳 =
  Σ[ x ∈ 𝕌[ proj₁ 𝑳 ] ] Σ[ y ∈ 𝕌[ proj₁ 𝑳 ] ] Σ[ z ∈ 𝕌[ proj₁ 𝑳 ] ]
    ( (¬ (x ≈ y)) × (¬ (x ≈ z)) × (¬ (y ≈ z)) )
  where open Setoid 𝔻[ proj₁ 𝑳 ] using ( _≈_ )

TwoBigCanopies : {m : ℕ} → (Fin m → FiniteLattice) → Type 0ℓ
TwoBigCanopies {m} 𝑳s =
  Σ[ i ∈ Fin m ] Σ[ j ∈ Fin m ]
    ( (¬ (i ≡ j))
    × HasThreeDistinct (toLattice (𝑳s i))
    × HasThreeDistinct (toLattice (𝑳s j)) )
```

Statement (C): for every family of at least two finite lattices, two of them big,
and properties `Pᵢ` core-free enforceable by them, a *single* group satisfies every
`Pᵢ` and realizes every `𝑳ᵢ` as an upper interval over a core-free subgroup.  (The
note's § 3 statement strengthens core-freeness to every proper subgroup between
`Hᵢ` and `G`; that refinement needs the proper-subgroup language and is deferred to
RP-1 with the proof.)

```agda
Statement-C : (ℓP : Level) → Type (lsuc 0ℓ ⊔ lsuc ℓP)
Statement-C ℓP =
  ∀ (n : ℕ) (𝑳s : Fin (2 + n) → FiniteLattice) (Ps : Fin (2 + n) → GroupProperty ℓP)
  → TwoBigCanopies 𝑳s
  → (∀ i → cfIE (Ps i) (toLattice (𝑳s i)))
  → Σ[ 𝒢 ∈ Group 0ℓ 0ℓ ]
      ( (∀ i → Ps i 𝒢)
      × (∀ i → Σ[ H ∈ Pred 𝕌[ proj₁ 𝒢 ] 0ℓ ] Σ[ H-sg ∈ IsSubgroup 𝒢 H ]
                 ( CoreFree 𝒢 H H-sg
                 × IntervalIso 𝒢 H H-sg (toLattice (𝑳s i)) )) )
```

The proof of (B) → (C) rests on the **parachute construction**
`𝒫(L₁, …, Lₙ)` — a bottom element covered by `n` atoms with `Lᵢ` the interval from
the `i`-th atom to the shared top — and on the Dedekind-rule argument that a
core-free representation of a parachute makes every canopy's bottom subgroup
core-free.  Both are RP-1 material (the construction needs finite-lattice surgery,
the argument needs Dedekind's rule and the antichain corollary), so they enter as
the named hypothesis record `ParachuteHypotheses`{.AgdaRecord}, and the meta-theorem
is stated as a schema conditional on it and on the core-free reduction.

```agda
record ParachuteHypotheses : Type (lsuc 0ℓ) where
  field
    -- The parachute lattice of a finite family of finite lattices.
    parachute : (n : ℕ) → (Fin (2 + n) → FiniteLattice) → FiniteLattice

    -- Its defining property: a core-free group representation of the
    -- parachute yields, for each canopy, a representation of that canopy
    -- over a core-free subgroup of the same group.
    canopy-intervals :
      (n : ℕ) (𝑳s : Fin (2 + n) → FiniteLattice)
      (r : GroupRepresentable (toLattice (parachute n 𝑳s)))
      → CoreFree  (GroupRepresentable.grp r) (GroupRepresentable.sub r)
                  (GroupRepresentable.isSubgroup r)
      → TwoBigCanopies 𝑳s
      → ∀ i → Σ[ H ∈ Pred 𝕌[ proj₁ (GroupRepresentable.grp r) ] 0ℓ ]
              Σ[ H-sg ∈ IsSubgroup (GroupRepresentable.grp r) H ]
                ( CoreFree (GroupRepresentable.grp r) H H-sg
                × IntervalIso (GroupRepresentable.grp r) H H-sg (toLattice (𝑳s i)) )

-- Theorem thm-wjd-1 of the note, as a statement.
thm-wjd-1-Statement : (ℓP : Level) → Type (lsuc 0ℓ ⊔ lsuc ℓP)
thm-wjd-1-Statement ℓP =
  (GroupFLRP-Statement → Statement-C ℓP) × (Statement-C ℓP → GroupFLRP-Statement)

-- The schema RP-1 will inhabit: the meta-theorem conditional on the
-- parachute construction and the core-free reduction.
thm-wjd-1-Schema : (ℓP : Level) → Type (lsuc 0ℓ ⊔ lsuc ℓP)
thm-wjd-1-Schema ℓP =
  ParachuteHypotheses → CoreFreeReduction → thm-wjd-1-Statement ℓP
```

By statement (C), exhibiting finitely many cf-IE classes with empty intersection
would give the FLRP a negative answer; that hunt is RP-3, over the catalog RP-2
builds on top of the definitions of this module.

---

[^1]: Sketch: take `𝒦` presented on a two-element carrier `{a , b}` with `a ≈ b`
      and all operations returning `a` (a one-element group presented redundantly),
      and `𝒢 = ℤ₂` on a propositional-equality carrier with `H` trivial.  The bare
      predicate `{(e , a) , (e , b) , (g , a)}` is closed under the product
      operations and lies between `H ×ᶠ 𝒦` and the full subuniverse, yet is neither
      `≈`-saturated nor mutually included with a pulled-back subgroup of `𝒢`, so the
      bare interval `[H ×ᶠ 𝒦 , full]` has three elements while `[H , full]` in
      `Sub(ℤ₂)` has two.  Requiring `respects`{.AgdaField} removes exactly this
      presentation junk.
