---
layout: default
file: "src/Classical/Structures/Lattice/OrdinalSum.lagda.md"
title: "Classical.Structures.Lattice.OrdinalSum module"
date: "2026-07-24"
author: "the agda-algebras development team"
---

### Ordinal sums of lattices {#classical-structures-lattice-ordinalsum}

This is the [Classical.Structures.Lattice.OrdinalSum][] module of the [Agda Universal Algebra Library][].

The **adjoined ordinal sum** of lattices `𝓛₁`{.AgdaBound} and `𝓛₂`{.AgdaBound} stacks
`𝓛₂`{.AgdaBound} on top of `𝓛₁`{.AgdaBound} and *glues* the top of `𝓛₁`{.AgdaBound}
to the bottom of `𝓛₂`{.AgdaBound}: every element of the lower summand lies below
every element of the upper one, and the two chosen extrema become a single element.

This is the operation denoted by `L ⊕ₐ M` in the small-lattice representations manuscript
([docs/papers/fin-lat-rep/SmallLatticeReps.tex](docs/papers/fin-lat-rep/SmallLatticeReps.tex),
§ Ordinal Sums).

The *unglued* ordinal sum, in which the top of the lower summand is covered by the
bottom of the upper, is the derived composite `(𝓛₁ ⊕ₐ chain₂) ⊕ₐ 𝓛₂`, gluing a
two-element chain in the middle leaves exactly one covering edge, so the glued form
is the module's single canonical primitive.

Because the sum glues at chosen extrema, the construction takes them as data: a
`TopOf 𝓛₁`{.AgdaFunction} and a `BottomOf 𝓛₂`{.AgdaFunction}
([Classical.Properties.Lattice][]).[^1]

#### Remarks on the design

+  **Gluing is by setoid equality, not element removal**.

   The carrier is the disjoint union `A ⊎ B` with the equivalence coarsened so that
   `inj₁ ⊤₁ ≈ inj₂ ⊥₂`; removing a point would require deciding equality with it,
   whereas coarsening is constructive and level-polymorphic.

   The amalgam setoid is isolated in `GlueSetoid`{.AgdaModule}, defined for *any* two
   pointed setoids: its equivalence is the pullback of the component equivalences
   along the two *retractions* that collapse the opposite summand to the basepoint.

   This pullback presentation makes reflexivity, symmetry, and transitivity
   componentwise — no case analysis — and on each summand it restricts to the
   original equivalence, while across summands it holds exactly at the glue.

   It is carried by a *record indexed by its two endpoints*, not by a defined
   relation; see the section
   [Why a record and not a relation](#why-a-record-and-not-a-relation) below.[^2]

+  **The operations never cross the glue**.

   Meet sends a mixed pair to its lower summand's member and join to its upper one,
   so the eight lattice equations hold by case analysis with the component laws on
   the diagonal cases and definitional reduction elsewhere; only the *congruence* of
   the operations interacts with the glue, and there the extremum laws (`x ∧ ⊤ ≈ x`,
   `⊥ ∨ x ≈ x`, and their mirrors) discharge every case.

The first consumer is the FLRP closure toolkit ([FLRP.Closure][]), which represents
the ordinal sum as a congruence lattice whenever its summands are so representable.[^3]

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Lattice.OrdinalSum where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Product          using ( _,_ ; _×_ ; proj₁ )
open import Data.Sum.Base         using ( _⊎_ ; inj₁ ; inj₂ )
open import Level                 using ( Level ; _⊔_ )
open import Relation.Binary       using ( Setoid )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice        using  ( module Lattice-Order
                                                       ; TopOf ; BottomOf )
open import Classical.Signatures.Lattice        using  ( Sig-Lattice )
open import Classical.Structures.Lattice.Basic  using  ( Lattice ; module Lattice-Op
                                                       ; setoidEqsToLattice )
open import Setoid.Algebras.Basic               using  ( 𝕌[_] ; 𝔻[_] ; Algebra )

private variable α ρ β σ : Level
```
-->

#### The amalgam of two pointed setoids

`GlueSetoid`{.AgdaModule} `𝐴 a₀ 𝐵 b₀` is the disjoint union of the carriers with
`inj₁ a₀` and `inj₂ b₀` identified.  The equivalence is stated through the two
retractions: `retractˡ`{.AgdaFunction} keeps the left summand and collapses the right
to `a₀`, and `retractʳ`{.AgdaFunction} mirrors it; two elements are equal exactly
when both retractions agree.

On `inj₁`/`inj₁` pairs the right retraction is constantly `b₀`, so the condition is
the left equivalence (dually on `inj₂`/`inj₂`), and on mixed pairs it says precisely
"left component at `a₀`, right component at `b₀`."

```agda
module GlueSetoid
  (𝐴 : Setoid α ρ)
  (a₀ : Setoid.Carrier 𝐴)  -- ASSUMPTION: 𝑨 is nonempty
  (𝐵 : Setoid β σ)
  (b₀ : Setoid.Carrier 𝐵)   -- ASSUMPTION: 𝑩 is nonempty
  where
  open Setoid 𝐴 renaming  ( Carrier to A ; _≈_ to _≈₁_
                          ; refl to refl₁ ; sym to sym₁ ; trans to trans₁ )

  open Setoid 𝐵 renaming  ( Carrier to B ; _≈_ to _≈₂_
                          ; refl to refl₂ ; sym to sym₂ ; trans to trans₂ )

  -- Keep the left summand; collapse the right to the left basepoint.
  retractˡ : A ⊎ B → A
  retractˡ (inj₁ x) = x
  retractˡ (inj₂ _) = a₀

  -- Keep the right summand; collapse the left to the right basepoint.
  retractʳ : A ⊎ B → B
  retractʳ (inj₁ _) = b₀
  retractʳ (inj₂ y) = y

  -- Glued equality: both retractions agree.  A *record* indexed by the two
  -- endpoints, not a defined relation — see the note below.
  record _≈ᵍ_ (x y : A ⊎ B) : Type (ρ ⊔ σ) where
    constructor _∧ᵍ_
    field
      ≈ˡ : retractˡ x ≈₁ retractˡ y
      ≈ʳ : retractʳ x ≈₂ retractʳ y

  infix 4 _≈ᵍ_
  infixr 4 _∧ᵍ_
  open _≈ᵍ_ public

  open Setoid
  -- The amalgam setoid: A ⊎ B with the basepoints identified.
  glueSetoid : Setoid (α ⊔ β) (ρ ⊔ σ)
  glueSetoid .Carrier = A ⊎ B
  glueSetoid ._≈_ = _≈ᵍ_
  glueSetoid .isEquivalence =
    record  { refl   = refl₁ ∧ᵍ refl₂
            ; sym    = λ (e₁ ∧ᵍ e₂) → sym₁ e₁ ∧ᵍ sym₂ e₂
            ; trans  = λ (d₁ ∧ᵍ d₂) (e₁ ∧ᵍ e₂) → trans₁ d₁ e₁ ∧ᵍ trans₂ d₂ e₂
            }

  -- The glue itself: the two basepoints are identified.
  glue-≈ : inj₁ a₀ ≈ᵍ inj₂ b₀
  glue-≈ = refl₁ ∧ᵍ refl₂

  -- Injections are ≈-embeddings: the intro forms supply the constant component.
  ≈ᵍ-inj₁ : {x y : A} → x ≈₁ y → inj₁ x ≈ᵍ inj₁ y
  ≈ᵍ-inj₁ e = e ∧ᵍ refl₂

  ≈ᵍ-inj₂ : {x y : B} → x ≈₂ y → inj₂ x ≈ᵍ inj₂ y
  ≈ᵍ-inj₂ e = refl₁ ∧ᵍ e
```

The elimination forms are the two fields:

+  `≈ˡ`{.AgdaField} of an `inj₁`/`inj₁` equation is the left equivalence,
+  `≈ʳ`{.AgdaField} of an `inj₂`/`inj₂` equation the right one,

and on a mixed pair the two fields are exactly the basepoint conditions.


#### Why a record and not a relation {#why-a-record-and-not-a-relation}

The mathematically obvious phrasing of the same relation is the defined pullback

    x ≈ᵍ y = (retractˡ x ≈₁ retractˡ y) × (retractʳ x ≈₂ retractʳ y)

and that phrasing is hostile to Agda's unifier.

A *defined* relation is unfolded whenever the type checker must infer an implicit
endpoint whose type mentions it, leaving constraints whose metavariables sit under
the retractions,

    retractˡ _x = retractˡ x    retractʳ _x = retractʳ x

which are permanently stuck, for two independent reasons.

1. The retractions are genuinely non-injective (each collapses a whole summand to a
   basepoint), so the constraint cannot be inverted.

2. The carrier `A ⊎ B` is a datatype without an η-rule, so the metavariable cannot be
   η-expanded into components the way a `Σ`-typed one can.

The sibling product construction ([Classical.Structures.Lattice.Product][]) defines
its equivalence through `proj₁`/`proj₂`, which are just as non-injective — but there
`Σ`-η lets Agda solve the projected metas componentwise, so inference never breaks.
The failure needs exactly the combination present here: defined relation,
non-injective non-variable head, no η on the carrier.

A one-constructor record *indexed by the two endpoints* keeps every good property
of the pullback presentation:

+  reflexivity, symmetry, and transitivity are still componentwise with no case analysis;
+  on each summand the fields still reduce to that summand's equivalence, and across
   summands to the glue condition;
+  η keeps proofs pair-like.

Moreover, it makes the relation a *record type former, hence injective for unification*.

A constraint `?x ≈ᵍ ?y ≟ a ≈ᵍ b` now solves the endpoints *before* any retraction is
exposed, so implicit-endpoint lemmas (`Setoid.refl`/`sym`/`trans` at `≈ᵍ`,
congruences passed under-applied to record-constructor arguments,
parameterized-module applications) all infer.  The "canary" below fails to type-check
the moment that property is lost.[^4]

The idiom generalizes: *any* relation defined by restriction along a non-injective
map — including relations built downstream through these same retractions — should
be a record indexed by its endpoints rather than a definition.

```agda
  -- Canary: an implicit endpoint under `_≈ᵍ_` must be inferable.  This fails
  -- with [UnsolvedMetaVariables] if `_≈ᵍ_` ever reverts to a defined relation.
  _ : ∀ x → x ≈ᵍ x
  _ = λ x → Setoid.refl glueSetoid
```

#### The ordinal-sum construction

`LatticeOrdinalSum`{.AgdaModule} packages the development for fixed summands and
extremum choices; opening it provides the glued carrier, the operations with
their congruences and equations, the sum lattice, and the characterization of its
order.

In this module we adopt the following notational convention: for `i ∈ {1, 2}`,

+ `𝓛ᵢ` denotes a full lattice structure: carrier, operations, and lattice laws;
+ `𝑳ᵢ` denotes the carrier and operations of the lattice `𝓛ᵢ`;
+ `Lᵢ` denotes just the carrier of `𝓛ᵢ`.

```agda
module LatticeOrdinalSum

  (𝓛₁ : Lattice α ρ)
  ((⊤₁ , ⊤₁max) : TopOf 𝓛₁)      -- ASSUMPTION: 𝓛₁ has maximal element ⊤₁
  (𝓛₂ : Lattice β σ)
  ((⊥₂ , ⊥₂min) : BottomOf 𝓛₂)      -- ASSUMPTION: 𝓛₂ has minimal element ⊥₂
  where
  private
    𝑳₁ : Algebra {𝑆 = Sig-Lattice} α ρ
    𝑳₁ = proj₁ 𝓛₁
    𝑳₂ : Algebra {𝑆 = Sig-Lattice} β σ
    𝑳₂   = proj₁ 𝓛₂
    L₁ : Type α
    L₁ = 𝕌[ 𝑳₁ ]
    L₂ : Type β
    L₂ = 𝕌[ 𝑳₂ ]

  open Setoid 𝔻[ 𝑳₁ ] using () renaming ( _≈_ to _≈₁_ ; refl to refl₁ ; sym to sym₁ ; trans to trans₁ )
  open Setoid 𝔻[ 𝑳₂ ] using () renaming ( _≈_ to _≈₂_ ; refl to refl₂ ; sym to sym₂ ; trans to trans₂ )

  open Lattice-Op 𝓛₁ using ()
    renaming ( _∧_ to _∧₁_ ; _∨_ to _∨₁_ ; ∧-cong to ∧₁-cong ; ∨-cong to ∨₁-cong
             ; ∧-assoc-law to ∧₁-assoc ; ∧-comm-law to ∧₁-comm ; ∧-idem-law to ∧₁-idem
             ; ∨-assoc-law to ∨₁-assoc ; ∨-comm-law to ∨₁-comm ; ∨-idem-law to ∨₁-idem
             ; absorbˡ-law to absorbˡ₁ ; absorbʳ-law to absorbʳ₁ )
  open Lattice-Op 𝓛₂ using ()
    renaming ( _∧_ to _∧₂_ ; _∨_ to _∨₂_ ; ∧-cong to ∧₂-cong ; ∨-cong to ∨₂-cong
             ; ∧-assoc-law to ∧₂-assoc ; ∧-comm-law to ∧₂-comm ; ∧-idem-law to ∧₂-idem
             ; ∨-assoc-law to ∨₂-assoc ; ∨-comm-law to ∨₂-comm ; ∨-idem-law to ∨₂-idem
             ; absorbˡ-law to absorbˡ₂ ; absorbʳ-law to absorbʳ₂ )

  open Lattice-Order 𝓛₁ using () renaming ( _≤_ to _≤₁_ ; ≤-via-∨ to ≤-via-∨₁ )
  open Lattice-Order 𝓛₂ using () renaming ( _≤_ to _≤₂_ ; ≤-via-∨ to ≤-via-∨₂ )
```

The absorption behaviour of the chosen extrema, in the eight one-sided forms the
case analyses below consume.  Note that `x ≤₁ ⊤₁` *is* `x ∧₁ ⊤₁ ≈₁ x` and
`⊥₂ ≤₂ x` *is* `⊥₂ ∧₂ x ≈₂ ⊥₂`, definitionally, so half of these are the
universal properties themselves.

```agda
  private
    x∧⊤ : ∀ x → x ∧₁ ⊤₁ ≈₁ x
    x∧⊤ x = ⊤₁max x

    ⊤∧x : ∀ x → ⊤₁ ∧₁ x ≈₁ x
    ⊤∧x x = trans₁ ∧₁-comm (x∧⊤ x)

    x∨⊤ : ∀ x → x ∨₁ ⊤₁ ≈₁ ⊤₁
    x∨⊤ x = ≤-via-∨₁ (⊤₁max x)

    ⊤∨x : ∀ x → ⊤₁ ∨₁ x ≈₁ ⊤₁
    ⊤∨x x = trans₁ ∨₁-comm (x∨⊤ x)

    ⊥∧x : ∀ x → ⊥₂ ∧₂ x ≈₂ ⊥₂
    ⊥∧x x = ⊥₂min x

    x∧⊥ : ∀ x → x ∧₂ ⊥₂ ≈₂ ⊥₂
    x∧⊥ x = trans₂ ∧₂-comm (⊥∧x x)

    ⊥∨x : ∀ x → ⊥₂ ∨₂ x ≈₂ x
    ⊥∨x x = ≤-via-∨₂ (⊥₂min x)

    x∨⊥ : ∀ x → x ∨₂ ⊥₂ ≈₂ x
    x∨⊥ x = trans₂ ∨₂-comm (⊥∨x x)
```

**The glued carrier at the two chosen extrema**.

```agda
  open GlueSetoid 𝔻[ 𝑳₁ ] ⊤₁ 𝔻[ 𝑳₂ ] ⊥₂ public

  private
    A⊎B : Type (α ⊔ β)
    A⊎B = L₁ ⊎ L₂
```

**Meet and join**.

A mixed meet lands in the lower summand and a mixed join in the
upper one — the lower summand lies entirely below the upper.

```agda
  _∧ᵒ_ : A⊎B → A⊎B → A⊎B
  inj₁ x ∧ᵒ inj₁ y = inj₁ (x ∧₁ y)
  inj₁ x ∧ᵒ inj₂ y = inj₁ x
  inj₂ x ∧ᵒ inj₁ y = inj₁ y
  inj₂ x ∧ᵒ inj₂ y = inj₂ (x ∧₂ y)

  _∨ᵒ_ : A⊎B → A⊎B → A⊎B
  inj₁ x ∨ᵒ inj₁ y = inj₁ (x ∨₁ y)
  inj₁ x ∨ᵒ inj₂ y = inj₂ y
  inj₂ x ∨ᵒ inj₁ y = inj₂ x
  inj₂ x ∨ᵒ inj₂ y = inj₂ (x ∨₂ y)

  infixr 7 _∧ᵒ_
  infixr 6 _∨ᵒ_
```

**Congruence**.

This is the one place the glue matters.  Each of the sixteen constructor combinations
reduces to a pair of component goals; the diagonal combinations are the component
congruences, and every combination that crosses the glue is discharged by the
extremum-absorption lemmas above (an argument `≈ᵍ`-related across the glue pins its
left component to `⊤₁` or its right one to `⊥₂`, and absorption then collapses the
affected meet or join).

```agda
  ∧ᵒ-cong : ∀ {p q u v} → p ≈ᵍ q → u ≈ᵍ v → p ∧ᵒ u ≈ᵍ q ∧ᵒ v
```

<!--
```agda
  ∧ᵒ-cong {inj₁ _} {inj₁ _} {inj₁ _} {inj₁ _} (ea ∧ᵍ _) (fa ∧ᵍ _)   = ∧₁-cong ea fa ∧ᵍ refl₂
  ∧ᵒ-cong {inj₂ _} {inj₂ _} {inj₂ _} {inj₂ _} (_ ∧ᵍ eb) (_ ∧ᵍ fb)   = refl₁ ∧ᵍ ∧₂-cong eb fb

  ∧ᵒ-cong {inj₁ _} {inj₁ y} {inj₁ _} {inj₂ _} (ea ∧ᵍ _)  (fa ∧ᵍ _)  = trans₁ (∧₁-cong ea fa) (x∧⊤ y) ∧ᵍ refl₂
  ∧ᵒ-cong {inj₁ _} {inj₁ y} {inj₂ _} {inj₁ _} (ea ∧ᵍ _)  (fa ∧ᵍ _)  = trans₁ ea (trans₁ (sym₁ (x∧⊤ y)) (∧₁-cong refl₁ fa)) ∧ᵍ refl₂
  ∧ᵒ-cong {inj₁ _} {inj₂ _} {inj₁ _} {inj₁ v} (ea ∧ᵍ _)  (fa ∧ᵍ _)  = trans₁ (∧₁-cong ea fa) (⊤∧x v) ∧ᵍ refl₂
  ∧ᵒ-cong {inj₂ _} {inj₁ _} {inj₁ _} {inj₁ v} (ea ∧ᵍ _)  (fa ∧ᵍ _)  = trans₁ fa (trans₁ (sym₁ (⊤∧x v)) (∧₁-cong ea refl₁)) ∧ᵍ refl₂

  ∧ᵒ-cong {inj₁ _} {inj₁ _} {inj₂ _} {inj₂ _} (ea ∧ᵍ _)  _          = ea ∧ᵍ refl₂
  ∧ᵒ-cong {inj₂ _} {inj₂ _} {inj₁ _} {inj₁ _} _         (fa ∧ᵍ _)   = fa ∧ᵍ refl₂
  ∧ᵒ-cong {inj₁ _} {inj₂ _} {inj₂ _} {inj₁ _} (ea ∧ᵍ _)  (fa ∧ᵍ _)  = trans₁ ea fa ∧ᵍ refl₂
  ∧ᵒ-cong {inj₂ _} {inj₁ _} {inj₁ _} {inj₂ _} (ea ∧ᵍ _)  (fa ∧ᵍ _)  = trans₁ fa ea ∧ᵍ refl₂
  ∧ᵒ-cong {inj₁ _} {inj₂ _} {inj₁ _} {inj₂ _} (ea ∧ᵍ eb) (fa ∧ᵍ fb) = trans₁ (∧₁-cong ea fa) ∧₁-idem ∧ᵍ trans₂ (sym₂ ∧₂-idem) (∧₂-cong eb fb)
  ∧ᵒ-cong {inj₂ _} {inj₁ _} {inj₂ _} {inj₁ _} (ea ∧ᵍ eb) (fa ∧ᵍ fb) = trans₁ (sym₁ ∧₁-idem) (∧₁-cong ea fa) ∧ᵍ trans₂ (∧₂-cong eb fb) ∧₂-idem

  ∧ᵒ-cong {inj₁ _} {inj₂ _} {inj₂ _} {inj₂ v} (ea ∧ᵍ eb) _          = ea ∧ᵍ trans₂ (sym₂ (⊥∧x v)) (∧₂-cong eb refl₂)
  ∧ᵒ-cong {inj₂ _} {inj₁ _} {inj₂ u} {inj₂ _} (ea ∧ᵍ eb) _          = ea ∧ᵍ trans₂ (∧₂-cong eb refl₂) (⊥∧x u)
  ∧ᵒ-cong {inj₂ _} {inj₂ y} {inj₁ _} {inj₂ _} _         (fa ∧ᵍ fb)  = fa ∧ᵍ trans₂ (sym₂ (x∧⊥ y)) (∧₂-cong refl₂ fb)
  ∧ᵒ-cong {inj₂ x} {inj₂ _} {inj₂ _} {inj₁ _} _         (fa ∧ᵍ fb)  = fa ∧ᵍ trans₂ (∧₂-cong refl₂ fb) (x∧⊥ x)
```
-->

`∨ᵒ-cong`{.AgdaFunction} is the join half of the same argument, with the same
sixteen-case structure and the same reason for each case: diagonal combinations are
the component congruences, and combinations crossing the glue are absorbed, this
time by the `⊤`-absorption lemmas rather than the `⊥`-absorption ones, since it is
the top of the lower summand that a join can reach.

```agda
  ∨ᵒ-cong : ∀ {p q u v} → p ≈ᵍ q → u ≈ᵍ v → p ∨ᵒ u ≈ᵍ q ∨ᵒ v
```

<!--
```agda
  ∨ᵒ-cong {inj₁ _} {inj₁ _} {inj₁ _} {inj₁ _} (ea ∧ᵍ _)  (fa ∧ᵍ _)  = ∨₁-cong ea fa ∧ᵍ refl₂
  ∨ᵒ-cong {inj₂ _} {inj₂ _} {inj₂ _} {inj₂ _} (_ ∧ᵍ eb)  (_ ∧ᵍ fb)  = refl₁ ∧ᵍ ∨₂-cong eb fb

  ∨ᵒ-cong {inj₁ x} {inj₁ _} {inj₁ _} {inj₂ _} (ea ∧ᵍ _)  (fa ∧ᵍ fb) = trans₁ (∨₁-cong refl₁ fa) (x∨⊤ x) ∧ᵍ fb
  ∨ᵒ-cong {inj₁ _} {inj₁ y} {inj₂ _} {inj₁ _} (ea ∧ᵍ _)  (fa ∧ᵍ fb) = trans₁ (sym₁ (x∨⊤ y)) (∨₁-cong refl₁ fa) ∧ᵍ fb
  ∨ᵒ-cong {inj₁ _} {inj₂ _} {inj₁ u} {inj₁ _} (ea ∧ᵍ eb) (fa ∧ᵍ _)  = trans₁ (∨₁-cong ea refl₁) (⊤∨x u) ∧ᵍ eb
  ∨ᵒ-cong {inj₂ _} {inj₁ _} {inj₁ _} {inj₁ v} (ea ∧ᵍ eb) (fa ∧ᵍ _)  = trans₁ (sym₁ (⊤∨x v)) (∨₁-cong ea refl₁) ∧ᵍ eb

  ∨ᵒ-cong {inj₁ _} {inj₁ _} {inj₂ _} {inj₂ _} _         (_ ∧ᵍ fb)   = refl₁ ∧ᵍ fb
  ∨ᵒ-cong {inj₂ _} {inj₂ _} {inj₁ _} {inj₁ _} (_ ∧ᵍ eb)  _          = refl₁ ∧ᵍ eb
  ∨ᵒ-cong {inj₁ _} {inj₂ _} {inj₂ _} {inj₁ _} (ea ∧ᵍ eb) (fa ∧ᵍ fb) = refl₁ ∧ᵍ trans₂ fb eb
  ∨ᵒ-cong {inj₂ _} {inj₁ _} {inj₁ _} {inj₂ _} (ea ∧ᵍ eb) (fa ∧ᵍ fb) = refl₁ ∧ᵍ trans₂ eb fb
  ∨ᵒ-cong {inj₁ _} {inj₂ _} {inj₁ _} {inj₂ _} (ea ∧ᵍ eb) (fa ∧ᵍ fb) = trans₁ (∨₁-cong ea fa) ∨₁-idem ∧ᵍ trans₂ (sym₂ ∨₂-idem) (∨₂-cong eb fb)
  ∨ᵒ-cong {inj₂ _} {inj₁ _} {inj₂ _} {inj₁ _} (ea ∧ᵍ eb) (fa ∧ᵍ fb) = trans₁ (sym₁ ∨₁-idem) (∨₁-cong ea fa) ∧ᵍ trans₂ (∨₂-cong eb fb) ∨₂-idem

  ∨ᵒ-cong {inj₁ _} {inj₂ _} {inj₂ _} {inj₂ v} (ea ∧ᵍ eb) (_ ∧ᵍ fb)  = refl₁ ∧ᵍ trans₂ fb (trans₂ (sym₂ (⊥∨x v)) (∨₂-cong eb refl₂))
  ∨ᵒ-cong {inj₂ _} {inj₁ _} {inj₂ u} {inj₂ _} (ea ∧ᵍ eb) (_ ∧ᵍ fb)  = refl₁ ∧ᵍ trans₂ (∨₂-cong eb refl₂) (trans₂ (⊥∨x u) fb)
  ∨ᵒ-cong {inj₂ _} {inj₂ y} {inj₁ _} {inj₂ _} (_ ∧ᵍ eb)  (_ ∧ᵍ fb)  = refl₁ ∧ᵍ trans₂ eb (trans₂ (sym₂ (x∨⊥ y)) (∨₂-cong refl₂ fb))
  ∨ᵒ-cong {inj₂ x} {inj₂ _} {inj₂ _} {inj₁ _} (_ ∧ᵍ eb)  (_ ∧ᵍ fb)  = refl₁ ∧ᵍ trans₂ (∨₂-cong refl₂ fb) (trans₂ (x∨⊥ x) eb)
```
-->

**The eight equations**.

The operations never cross the glue, so every mixed case reduces definitionally and
is closed by reflexivity; the diagonal cases are the component laws, and the two
absorption laws additionally consume one idempotency step in their
`inj₂`-meets-`inj₁` (resp. mirrored) case.

```agda
  ∧ᵒ-assoc : ∀ {p q r} → (p ∧ᵒ q) ∧ᵒ r ≈ᵍ p ∧ᵒ (q ∧ᵒ r)
  ∧ᵒ-assoc {inj₁ _} {inj₁ _} {inj₁ _} = ∧₁-assoc ∧ᵍ refl₂
  ∧ᵒ-assoc {inj₂ _} {inj₂ _} {inj₂ _} = refl₁ ∧ᵍ ∧₂-assoc

  ∧ᵒ-assoc {inj₁ _} {inj₁ _} {inj₂ _} = refl₁ ∧ᵍ refl₂
  ∧ᵒ-assoc {inj₁ _} {inj₂ _} {inj₁ _} = refl₁ ∧ᵍ refl₂
  ∧ᵒ-assoc {inj₂ _} {inj₁ _} {inj₁ _} = refl₁ ∧ᵍ refl₂
  ∧ᵒ-assoc {inj₁ _} {inj₂ _} {inj₂ _} = refl₁ ∧ᵍ refl₂
  ∧ᵒ-assoc {inj₂ _} {inj₁ _} {inj₂ _} = refl₁ ∧ᵍ refl₂
  ∧ᵒ-assoc {inj₂ _} {inj₂ _} {inj₁ _} = refl₁ ∧ᵍ refl₂

  ∧ᵒ-comm : ∀ {p q} → p ∧ᵒ q ≈ᵍ q ∧ᵒ p
  ∧ᵒ-comm {inj₁ _} {inj₁ _} = ∧₁-comm ∧ᵍ refl₂
  ∧ᵒ-comm {inj₁ _} {inj₂ _} = refl₁ ∧ᵍ refl₂
  ∧ᵒ-comm {inj₂ _} {inj₁ _} = refl₁ ∧ᵍ refl₂
  ∧ᵒ-comm {inj₂ _} {inj₂ _} = refl₁ ∧ᵍ ∧₂-comm

  ∧ᵒ-idem : ∀ {p} → p ∧ᵒ p ≈ᵍ p
  ∧ᵒ-idem {inj₁ _} = ∧₁-idem ∧ᵍ refl₂
  ∧ᵒ-idem {inj₂ _} = refl₁ ∧ᵍ ∧₂-idem

  ∨ᵒ-assoc : ∀ {p q r} → (p ∨ᵒ q) ∨ᵒ r ≈ᵍ p ∨ᵒ (q ∨ᵒ r)
  ∨ᵒ-assoc {inj₁ _} {inj₁ _} {inj₁ _} = ∨₁-assoc ∧ᵍ refl₂
  ∨ᵒ-assoc {inj₂ _} {inj₂ _} {inj₂ _} = refl₁ ∧ᵍ ∨₂-assoc
  ∨ᵒ-assoc {inj₁ _} {inj₁ _} {inj₂ _} = refl₁ ∧ᵍ refl₂
  ∨ᵒ-assoc {inj₁ _} {inj₂ _} {inj₁ _} = refl₁ ∧ᵍ refl₂
  ∨ᵒ-assoc {inj₁ _} {inj₂ _} {inj₂ _} = refl₁ ∧ᵍ refl₂
  ∨ᵒ-assoc {inj₂ _} {inj₁ _} {inj₁ _} = refl₁ ∧ᵍ refl₂
  ∨ᵒ-assoc {inj₂ _} {inj₁ _} {inj₂ _} = refl₁ ∧ᵍ refl₂
  ∨ᵒ-assoc {inj₂ _} {inj₂ _} {inj₁ _} = refl₁ ∧ᵍ refl₂

  ∨ᵒ-comm : ∀ {p q} → p ∨ᵒ q ≈ᵍ q ∨ᵒ p
  ∨ᵒ-comm {inj₁ _} {inj₁ _} = ∨₁-comm ∧ᵍ refl₂
  ∨ᵒ-comm {inj₁ _} {inj₂ _} = refl₁ ∧ᵍ refl₂
  ∨ᵒ-comm {inj₂ _} {inj₁ _} = refl₁ ∧ᵍ refl₂
  ∨ᵒ-comm {inj₂ _} {inj₂ _} = refl₁ ∧ᵍ ∨₂-comm

  ∨ᵒ-idem : ∀ {p} → p ∨ᵒ p ≈ᵍ p
  ∨ᵒ-idem {inj₁ _} = ∨₁-idem ∧ᵍ refl₂
  ∨ᵒ-idem {inj₂ _} = refl₁ ∧ᵍ ∨₂-idem

  absorbˡᵒ : ∀ {p q} → p ∧ᵒ (p ∨ᵒ q) ≈ᵍ p
  absorbˡᵒ {inj₁ _} {inj₁ _} = absorbˡ₁ ∧ᵍ refl₂
  absorbˡᵒ {inj₁ _} {inj₂ _} = refl₁ ∧ᵍ refl₂
  absorbˡᵒ {inj₂ _} {inj₁ _} = refl₁ ∧ᵍ ∧₂-idem
  absorbˡᵒ {inj₂ _} {inj₂ _} = refl₁ ∧ᵍ absorbˡ₂

  absorbʳᵒ : ∀ {p q} → (p ∧ᵒ q) ∨ᵒ p ≈ᵍ p
  absorbʳᵒ {inj₁ _} {inj₁ _} = absorbʳ₁ ∧ᵍ refl₂
  absorbʳᵒ {inj₁ _} {inj₂ _} = ∨₁-idem ∧ᵍ refl₂
  absorbʳᵒ {inj₂ _} {inj₁ _} = refl₁ ∧ᵍ refl₂
  absorbʳᵒ {inj₂ _} {inj₂ _} = refl₁ ∧ᵍ absorbʳ₂

```

Assembling through the setoid-level builder yields the ordinal sum.  Every
argument is passed under-applied: the record presentation of `_≈ᵍ_`{.AgdaRecord}
lets Agda recover each implicit endpoint from the expected type, so none of them
has to be forwarded by hand.

```agda
  ⊕-Lattice : Lattice (α ⊔ β) (ρ ⊔ σ)
  ⊕-Lattice = setoidEqsToLattice glueSetoid _∧ᵒ_ _∨ᵒ_
    ∧ᵒ-cong ∨ᵒ-cong
    ∧ᵒ-assoc ∧ᵒ-comm ∧ᵒ-idem
    ∨ᵒ-assoc ∨ᵒ-comm ∨ᵒ-idem
    absorbˡᵒ absorbʳᵒ
```

**The sum order, characterized**.

The meet order of the sum unfolds definitionally on each constructor combination:
within a summand it is that summand's order, everything low is below everything high,
and the only way an upper element sits below a lower one is at the glue.  The four
lemmas name these unfoldings for consumers.

```agda
  open Lattice-Order ⊕-Lattice using () renaming ( _≤_ to _≤ᵒ_ )

  -- Within the lower summand, the sum order is the lower order.
  ≤ᵒ-inj₁ : {x y : L₁} → x ≤₁ y → inj₁ x ≤ᵒ inj₁ y
  ≤ᵒ-inj₁ e = e ∧ᵍ refl₂

  ≤ᵒ-inj₁-elim : {x y : L₁} → inj₁ x ≤ᵒ inj₁ y → x ≤₁ y
  ≤ᵒ-inj₁-elim = ≈ˡ

  -- Within the upper summand, the sum order is the upper order.
  ≤ᵒ-inj₂ : {x y : L₂} → x ≤₂ y → inj₂ x ≤ᵒ inj₂ y
  ≤ᵒ-inj₂ e = refl₁ ∧ᵍ e

  ≤ᵒ-inj₂-elim : {x y : L₂} → inj₂ x ≤ᵒ inj₂ y → x ≤₂ y
  ≤ᵒ-inj₂-elim = ≈ʳ

  -- Everything in the lower summand is below everything in the upper one.
  ≤ᵒ-up : {x : L₁} {y : L₂} → inj₁ x ≤ᵒ inj₂ y
  ≤ᵒ-up = refl₁ ∧ᵍ refl₂

  -- An upper element below a lower one forces both to the glue ...
  ≤ᵒ-down-elim : {x : L₂} {y : L₁}
    → inj₂ x ≤ᵒ (inj₁ y) → (y ≈₁ ⊤₁) × (x ≈₂ ⊥₂)
  ≤ᵒ-down-elim (p ∧ᵍ q) = p , sym₂ q

  -- ... and, at the glue, it does sit below.
  ≤ᵒ-down : {x : L₂} {y : L₁}
    → y ≈₁ ⊤₁ → x ≈₂ ⊥₂ → inj₂ x ≤ᵒ inj₁ y
  ≤ᵒ-down y≈⊤ x≈⊥ = y≈⊤ ∧ᵍ sym₂ x≈⊥
```

**The sum operator**.

The standalone operator, for consumers who need only the lattice.

```agda
ordinalSum : (𝓛₁ : Lattice α ρ) → TopOf 𝓛₁ → (𝓛₂ : Lattice β σ) → BottomOf 𝓛₂
  → Lattice (α ⊔ β) (ρ ⊔ σ)
ordinalSum 𝓛₁ t 𝓛₂ b = LatticeOrdinalSum.⊕-Lattice 𝓛₁ t 𝓛₂ b
```

--------------------------------------

[^1]: General lattices need not have extrema, and threading the choice keeps the
      construction total and the resulting carrier syntactically predictable (the
      corollaries that adjoin a fresh extremum to a lattice instantiate a summand at
      `chain₂` and its concrete `0`/`1`).

[^2]: The same idiom should be applied to any relation built by restriction along a non-injective map.

[^3]: See Work Package 5 (WP-5) of [the roadmap](docs/notes/flrp-research-roadmap.md).

[^4]: The full failure analysis, the minimal reproduction, and the rejected
      alternatives (a four-constructor inductive family, an `opaque` block, an
      injectivity pragma) are in
      [Issue #504](https://github.com/ualib/agda-algebras/issues/504).
