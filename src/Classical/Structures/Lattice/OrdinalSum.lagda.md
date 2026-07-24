---
layout: default
file: "src/Classical/Structures/Lattice/OrdinalSum.lagda.md"
title: "Classical.Structures.Lattice.OrdinalSum module"
date: "2026-07-24"
author: "the agda-algebras development team"
---

### Ordinal sums of lattices {#classical-structures-lattice-ordinalsum}

This is the [Classical.Structures.Lattice.OrdinalSum][] module of the [Agda Universal Algebra Library][].

The **adjoined ordinal sum** of lattices `𝑳₁`{.AgdaBound} and `𝑳₂`{.AgdaBound}
stacks `𝑳₂`{.AgdaBound} on top of `𝑳₁`{.AgdaBound} and *glues* the top of
`𝑳₁`{.AgdaBound} to the bottom of `𝑳₂`{.AgdaBound}: every element of the lower
summand lies below every element of the upper one, and the two chosen extrema
become a single element.  This is the operation `L ⊕ₐ M` of the small-lattice
representations manuscript (`docs/papers/fin-lat-rep/SmallLatticeReps.tex`,
§ Ordinal Sums); the *unglued* ordinal sum, in which the top of the lower summand
is covered by the bottom of the upper, is the derived composite
`(𝑳₁ ⊕ₐ chain₂) ⊕ₐ 𝑳₂` — gluing a two-element chain in the middle leaves exactly
one covering edge — so the glued form is the module's single canonical primitive.

Because the sum glues at *chosen* extrema, the construction takes them as data:
a `TopOf 𝑳₁`{.AgdaFunction} and a `BotOf 𝑳₂`{.AgdaFunction}
([Classical.Properties.Lattice][]).  General lattices need not have extrema, and
threading the choice keeps the construction total and the resulting carrier
syntactically predictable (the corollaries that adjoin a fresh extremum to a
lattice instantiate a summand at `chain₂` and its concrete `0`/`1`).

Two design points:

+  **Gluing is by setoid equality, not element removal.**  The carrier is the
   disjoint union `A ⊎ B` with the equivalence coarsened so that
   `inj₁ ⊤₁ ≈ inj₂ ⊥₂`; removing a point would require deciding equality with it,
   whereas coarsening is constructive and level-polymorphic.  The amalgam setoid is
   isolated in `GlueSetoid`{.AgdaModule} (the Cubical-port equality locus), defined
   for *any* two pointed setoids: its equivalence is the pullback of the component
   equivalences along the two **retractions** that collapse the opposite summand to
   the basepoint.  This pullback presentation makes reflexivity, symmetry, and
   transitivity componentwise — no case analysis — and on each summand it restricts
   to the original equivalence, while across summands it holds exactly at the glue.
+  **The operations never cross the glue.**  Meet sends a mixed pair to its lower
   summand's member and join to its upper one, so the eight lattice equations hold
   by case analysis with the component laws on the diagonal cases and definitional
   reduction elsewhere; only the *congruence* of the operations interacts with the
   glue, and there the extremum laws (`x ∧ ⊤ ≈ x`, `⊥ ∨ x ≈ x`, and their mirrors)
   discharge every case.

The first consumer is the FLRP closure toolkit ([FLRP.Closure][], work package
WP-5), which represents the ordinal sum as a congruence lattice whenever its
summands are so representable (roadmap § 3).

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Lattice.OrdinalSum where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Product          using ( _,_ ; _×_ ; proj₁ ; proj₂ )
open import Data.Sum.Base         using ( _⊎_ ; inj₁ ; inj₂ )
open import Level                 using ( Level ; _⊔_ )
open import Relation.Binary       using ( Setoid )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice  using ( module Lattice-Order ; TopOf ; BotOf )
open import Classical.Structures.Lattice  using ( Lattice ; module Lattice-Op
                                                ; setoidEqsToLattice )
open import Setoid.Algebras.Basic         using ( 𝕌[_] ; 𝔻[_] )

private variable α ρ β σ : Level
```
-->

#### The amalgam of two pointed setoids

`GlueSetoid`{.AgdaModule} `𝐴 a₀ 𝐵 b₀` is the disjoint union of the carriers with
`inj₁ a₀` and `inj₂ b₀` identified.  The equivalence is stated through the two
retractions: `retractˡ`{.AgdaFunction} keeps the left summand and collapses the
right to `a₀`, and `retractʳ`{.AgdaFunction} mirrors it; two elements are glued
equal exactly when both retractions agree.  On `inj₁`/`inj₁` pairs the right
retraction is constantly `b₀`, so the condition is the left equivalence (dually on
`inj₂`/`inj₂`), and on mixed pairs it says precisely "left component at `a₀`, right
component at `b₀`" — the glue and nothing else.

```agda
module GlueSetoid (𝐴 : Setoid α ρ) (a₀ : Setoid.Carrier 𝐴)
                  (𝐵 : Setoid β σ) (b₀ : Setoid.Carrier 𝐵) where
  private
    A = Setoid.Carrier 𝐴
    B = Setoid.Carrier 𝐵

  open Setoid 𝐴 using () renaming ( _≈_ to _≈₁_ ; refl to refl₁ ; sym to sym₁ ; trans to trans₁ )
  open Setoid 𝐵 using () renaming ( _≈_ to _≈₂_ ; refl to refl₂ ; sym to sym₂ ; trans to trans₂ )

  -- Keep the left summand; collapse the right to the left basepoint.
  retractˡ : A ⊎ B → A
  retractˡ (inj₁ x) = x
  retractˡ (inj₂ _) = a₀

  -- Keep the right summand; collapse the left to the right basepoint.
  retractʳ : A ⊎ B → B
  retractʳ (inj₁ _) = b₀
  retractʳ (inj₂ y) = y

  -- Glued equality: both retractions agree.
  _≈ᵍ_ : A ⊎ B → A ⊎ B → Type (ρ ⊔ σ)
  x ≈ᵍ y = (retractˡ x ≈₁ retractˡ y) × (retractʳ x ≈₂ retractʳ y)
  infix 4 _≈ᵍ_

  -- The amalgam setoid: A ⊎ B with the basepoints identified.
  glueSetoid : Setoid (α ⊔ β) (ρ ⊔ σ)
  glueSetoid = record
    { Carrier        = A ⊎ B
    ; _≈_            = _≈ᵍ_
    ; isEquivalence  = record
        { refl   = refl₁ , refl₂
        ; sym    = λ e → sym₁ (proj₁ e) , sym₂ (proj₂ e)
        ; trans  = λ d e → trans₁ (proj₁ d) (proj₁ e) , trans₂ (proj₂ d) (proj₂ e)
        }
    }

  -- The glue itself: the two basepoints are identified.
  glue-≈ : (inj₁ a₀) ≈ᵍ (inj₂ b₀)
  glue-≈ = refl₁ , refl₂

  -- Injections are ≈-embeddings: the intro forms supply the constant component.
  ≈ᵍ-inj₁ : {x y : A} → x ≈₁ y → (inj₁ x) ≈ᵍ (inj₁ y)
  ≈ᵍ-inj₁ e = e , refl₂

  ≈ᵍ-inj₂ : {x y : B} → x ≈₂ y → (inj₂ x) ≈ᵍ (inj₂ y)
  ≈ᵍ-inj₂ e = refl₁ , e
```

The elimination forms are the two projections: `proj₁` of an `inj₁`/`inj₁`
equation is the left equivalence, `proj₂` of an `inj₂`/`inj₂` equation the right
one, and on a mixed pair the two projections are exactly the basepoint conditions.

#### The ordinal-sum construction

`LatticeOrdinalSum`{.AgdaModule} packages the development for fixed summands and
extremum choices; opening it provides the glued carrier, the operations with
their congruences and equations, the sum lattice, and the characterization of its
order.

```agda
module LatticeOrdinalSum (𝑳₁ : Lattice α ρ) (t : TopOf 𝑳₁)
                         (𝑳₂ : Lattice β σ) (b : BotOf 𝑳₂) where
  private
    𝑨   = proj₁ 𝑳₁
    𝑩   = proj₁ 𝑳₂
    ⊤₁  = proj₁ t
    ⊥₂  = proj₁ b

  open Setoid 𝔻[ 𝑨 ] using () renaming ( _≈_ to _≈₁_ ; refl to refl₁ ; sym to sym₁ ; trans to trans₁ )
  open Setoid 𝔻[ 𝑩 ] using () renaming ( _≈_ to _≈₂_ ; refl to refl₂ ; sym to sym₂ ; trans to trans₂ )

  open Lattice-Op 𝑳₁ using ()
    renaming ( _∧_ to _∧₁_ ; _∨_ to _∨₁_ ; ∧-cong to ∧₁-cong ; ∨-cong to ∨₁-cong
             ; ∧-assoc-law to ∧₁-assoc ; ∧-comm-law to ∧₁-comm ; ∧-idem-law to ∧₁-idem
             ; ∨-assoc-law to ∨₁-assoc ; ∨-comm-law to ∨₁-comm ; ∨-idem-law to ∨₁-idem
             ; absorbˡ-law to absorbˡ₁ ; absorbʳ-law to absorbʳ₁ )
  open Lattice-Op 𝑳₂ using ()
    renaming ( _∧_ to _∧₂_ ; _∨_ to _∨₂_ ; ∧-cong to ∧₂-cong ; ∨-cong to ∨₂-cong
             ; ∧-assoc-law to ∧₂-assoc ; ∧-comm-law to ∧₂-comm ; ∧-idem-law to ∧₂-idem
             ; ∨-assoc-law to ∨₂-assoc ; ∨-comm-law to ∨₂-comm ; ∨-idem-law to ∨₂-idem
             ; absorbˡ-law to absorbˡ₂ ; absorbʳ-law to absorbʳ₂ )

  open Lattice-Order 𝑳₁ using () renaming ( _≤_ to _≤₁_ ; ≤-via-∨ to ≤-via-∨₁ )
  open Lattice-Order 𝑳₂ using () renaming ( _≤_ to _≤₂_ ; ≤-via-∨ to ≤-via-∨₂ )
```

The absorption behaviour of the chosen extrema, in the eight one-sided forms the
case analyses below consume.  Note that `x ≤₁ ⊤₁` *is* `x ∧₁ ⊤₁ ≈₁ x` and
`⊥₂ ≤₂ x` *is* `⊥₂ ∧₂ x ≈₂ ⊥₂`, definitionally, so half of these are the
universal properties themselves.

```agda
  private
    x∧⊤ : ∀ x → (x ∧₁ ⊤₁) ≈₁ x
    x∧⊤ x = proj₂ t x

    ⊤∧x : ∀ x → (⊤₁ ∧₁ x) ≈₁ x
    ⊤∧x x = trans₁ (∧₁-comm ⊤₁ x) (x∧⊤ x)

    x∨⊤ : ∀ x → (x ∨₁ ⊤₁) ≈₁ ⊤₁
    x∨⊤ x = ≤-via-∨₁ (proj₂ t x)

    ⊤∨x : ∀ x → (⊤₁ ∨₁ x) ≈₁ ⊤₁
    ⊤∨x x = trans₁ (∨₁-comm ⊤₁ x) (x∨⊤ x)

    ⊥∧x : ∀ x → (⊥₂ ∧₂ x) ≈₂ ⊥₂
    ⊥∧x x = proj₂ b x

    x∧⊥ : ∀ x → (x ∧₂ ⊥₂) ≈₂ ⊥₂
    x∧⊥ x = trans₂ (∧₂-comm x ⊥₂) (⊥∧x x)

    ⊥∨x : ∀ x → (⊥₂ ∨₂ x) ≈₂ x
    ⊥∨x x = ≤-via-∨₂ (proj₂ b x)

    x∨⊥ : ∀ x → (x ∨₂ ⊥₂) ≈₂ x
    x∨⊥ x = trans₂ (∨₂-comm x ⊥₂) (⊥∨x x)
```

The glued carrier, at the two chosen extrema.

```agda
  open GlueSetoid 𝔻[ 𝑨 ] ⊤₁ 𝔻[ 𝑩 ] ⊥₂ public

  private
    A⊎B : Type (α ⊔ β)
    A⊎B = 𝕌[ 𝑨 ] ⊎ 𝕌[ 𝑩 ]
```

Meet and join.  A mixed meet lands in the lower summand and a mixed join in the
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

**Congruence.**  This is the one place the glue matters.  Each of the sixteen
constructor combinations reduces to a pair of component goals; the diagonal
combinations are the component congruences, and every combination that crosses the
glue is discharged by the extremum-absorption lemmas above (an argument
`≈ᵍ`-related across the glue pins its left component to `⊤₁` or its right one to
`⊥₂`, and absorption then collapses the affected meet or join).

```agda
  ∧ᵒ-cong : ∀ {p q u v} → p ≈ᵍ q → u ≈ᵍ v → (p ∧ᵒ u) ≈ᵍ (q ∧ᵒ v)
  ∧ᵒ-cong {inj₁ x} {inj₁ y} {inj₁ u} {inj₁ v} (ea , _) (fa , _) =
    ∧₁-cong ea fa , refl₂
  ∧ᵒ-cong {inj₁ x} {inj₁ y} {inj₁ u} {inj₂ v} (ea , _) (fa , _) =
    trans₁ (∧₁-cong ea fa) (x∧⊤ y) , refl₂
  ∧ᵒ-cong {inj₁ x} {inj₁ y} {inj₂ u} {inj₁ v} (ea , _) (fa , _) =
    trans₁ ea (trans₁ (sym₁ (x∧⊤ y)) (∧₁-cong refl₁ fa)) , refl₂
  ∧ᵒ-cong {inj₁ x} {inj₁ y} {inj₂ u} {inj₂ v} (ea , _) _ =
    ea , refl₂
  ∧ᵒ-cong {inj₁ x} {inj₂ y} {inj₁ u} {inj₁ v} (ea , _) (fa , _) =
    trans₁ (∧₁-cong ea fa) (⊤∧x v) , refl₂
  ∧ᵒ-cong {inj₁ x} {inj₂ y} {inj₁ u} {inj₂ v} (ea , eb) (fa , fb) =
    trans₁ (∧₁-cong ea fa) (∧₁-idem ⊤₁) , trans₂ (sym₂ (∧₂-idem ⊥₂)) (∧₂-cong eb fb)
  ∧ᵒ-cong {inj₁ x} {inj₂ y} {inj₂ u} {inj₁ v} (ea , _) (fa , _) =
    trans₁ ea fa , refl₂
  ∧ᵒ-cong {inj₁ x} {inj₂ y} {inj₂ u} {inj₂ v} (ea , eb) _ =
    ea , trans₂ (sym₂ (⊥∧x v)) (∧₂-cong eb refl₂)
  ∧ᵒ-cong {inj₂ x} {inj₁ y} {inj₁ u} {inj₁ v} (ea , _) (fa , _) =
    trans₁ fa (trans₁ (sym₁ (⊤∧x v)) (∧₁-cong ea refl₁)) , refl₂
  ∧ᵒ-cong {inj₂ x} {inj₁ y} {inj₁ u} {inj₂ v} (ea , _) (fa , _) =
    trans₁ fa ea , refl₂
  ∧ᵒ-cong {inj₂ x} {inj₁ y} {inj₂ u} {inj₁ v} (ea , eb) (fa , fb) =
    trans₁ (sym₁ (∧₁-idem ⊤₁)) (∧₁-cong ea fa) , trans₂ (∧₂-cong eb fb) (∧₂-idem ⊥₂)
  ∧ᵒ-cong {inj₂ x} {inj₁ y} {inj₂ u} {inj₂ v} (ea , eb) _ =
    ea , trans₂ (∧₂-cong eb refl₂) (⊥∧x u)
  ∧ᵒ-cong {inj₂ x} {inj₂ y} {inj₁ u} {inj₁ v} _ (fa , _) =
    fa , refl₂
  ∧ᵒ-cong {inj₂ x} {inj₂ y} {inj₁ u} {inj₂ v} _ (fa , fb) =
    fa , trans₂ (sym₂ (x∧⊥ y)) (∧₂-cong refl₂ fb)
  ∧ᵒ-cong {inj₂ x} {inj₂ y} {inj₂ u} {inj₁ v} _ (fa , fb) =
    fa , trans₂ (∧₂-cong refl₂ fb) (x∧⊥ x)
  ∧ᵒ-cong {inj₂ x} {inj₂ y} {inj₂ u} {inj₂ v} (_ , eb) (_ , fb) =
    refl₁ , ∧₂-cong eb fb

  ∨ᵒ-cong : ∀ {p q u v} → p ≈ᵍ q → u ≈ᵍ v → (p ∨ᵒ u) ≈ᵍ (q ∨ᵒ v)
  ∨ᵒ-cong {inj₁ x} {inj₁ y} {inj₁ u} {inj₁ v} (ea , _) (fa , _) =
    ∨₁-cong ea fa , refl₂
  ∨ᵒ-cong {inj₁ x} {inj₁ y} {inj₁ u} {inj₂ v} (ea , _) (fa , fb) =
    trans₁ (∨₁-cong refl₁ fa) (x∨⊤ x) , fb
  ∨ᵒ-cong {inj₁ x} {inj₁ y} {inj₂ u} {inj₁ v} (ea , _) (fa , fb) =
    trans₁ (sym₁ (x∨⊤ y)) (∨₁-cong refl₁ fa) , fb
  ∨ᵒ-cong {inj₁ x} {inj₁ y} {inj₂ u} {inj₂ v} _ (_ , fb) =
    refl₁ , fb
  ∨ᵒ-cong {inj₁ x} {inj₂ y} {inj₁ u} {inj₁ v} (ea , eb) (fa , _) =
    trans₁ (∨₁-cong ea refl₁) (⊤∨x u) , eb
  ∨ᵒ-cong {inj₁ x} {inj₂ y} {inj₁ u} {inj₂ v} (ea , eb) (fa , fb) =
    trans₁ (∨₁-cong ea fa) (∨₁-idem ⊤₁) , trans₂ (sym₂ (∨₂-idem ⊥₂)) (∨₂-cong eb fb)
  ∨ᵒ-cong {inj₁ x} {inj₂ y} {inj₂ u} {inj₁ v} (ea , eb) (fa , fb) =
    refl₁ , trans₂ fb eb
  ∨ᵒ-cong {inj₁ x} {inj₂ y} {inj₂ u} {inj₂ v} (ea , eb) (_ , fb) =
    refl₁ , trans₂ fb (trans₂ (sym₂ (⊥∨x v)) (∨₂-cong eb refl₂))
  ∨ᵒ-cong {inj₂ x} {inj₁ y} {inj₁ u} {inj₁ v} (ea , eb) (fa , _) =
    trans₁ (sym₁ (⊤∨x v)) (∨₁-cong ea refl₁) , eb
  ∨ᵒ-cong {inj₂ x} {inj₁ y} {inj₁ u} {inj₂ v} (ea , eb) (fa , fb) =
    refl₁ , trans₂ eb fb
  ∨ᵒ-cong {inj₂ x} {inj₁ y} {inj₂ u} {inj₁ v} (ea , eb) (fa , fb) =
    trans₁ (sym₁ (∨₁-idem ⊤₁)) (∨₁-cong ea fa) , trans₂ (∨₂-cong eb fb) (∨₂-idem ⊥₂)
  ∨ᵒ-cong {inj₂ x} {inj₁ y} {inj₂ u} {inj₂ v} (ea , eb) (_ , fb) =
    refl₁ , trans₂ (∨₂-cong eb refl₂) (trans₂ (⊥∨x u) fb)
  ∨ᵒ-cong {inj₂ x} {inj₂ y} {inj₁ u} {inj₁ v} (_ , eb) _ =
    refl₁ , eb
  ∨ᵒ-cong {inj₂ x} {inj₂ y} {inj₁ u} {inj₂ v} (_ , eb) (_ , fb) =
    refl₁ , trans₂ eb (trans₂ (sym₂ (x∨⊥ y)) (∨₂-cong refl₂ fb))
  ∨ᵒ-cong {inj₂ x} {inj₂ y} {inj₂ u} {inj₁ v} (_ , eb) (_ , fb) =
    refl₁ , trans₂ (∨₂-cong refl₂ fb) (trans₂ (x∨⊥ x) eb)
  ∨ᵒ-cong {inj₂ x} {inj₂ y} {inj₂ u} {inj₂ v} (_ , eb) (_ , fb) =
    refl₁ , ∨₂-cong eb fb
```

**The eight equations.**  The operations never cross the glue, so every mixed
case reduces definitionally and is closed by reflexivity; the diagonal cases are
the component laws, and the two absorption laws additionally consume one
idempotency step in their `inj₂`-meets-`inj₁` (resp. mirrored) case.

```agda
  ∧ᵒ-assoc : ∀ p q r → ((p ∧ᵒ q) ∧ᵒ r) ≈ᵍ (p ∧ᵒ (q ∧ᵒ r))
  ∧ᵒ-assoc (inj₁ x) (inj₁ y) (inj₁ z) = ∧₁-assoc x y z , refl₂
  ∧ᵒ-assoc (inj₁ x) (inj₁ y) (inj₂ z) = refl₁ , refl₂
  ∧ᵒ-assoc (inj₁ x) (inj₂ y) (inj₁ z) = refl₁ , refl₂
  ∧ᵒ-assoc (inj₁ x) (inj₂ y) (inj₂ z) = refl₁ , refl₂
  ∧ᵒ-assoc (inj₂ x) (inj₁ y) (inj₁ z) = refl₁ , refl₂
  ∧ᵒ-assoc (inj₂ x) (inj₁ y) (inj₂ z) = refl₁ , refl₂
  ∧ᵒ-assoc (inj₂ x) (inj₂ y) (inj₁ z) = refl₁ , refl₂
  ∧ᵒ-assoc (inj₂ x) (inj₂ y) (inj₂ z) = refl₁ , ∧₂-assoc x y z

  ∧ᵒ-comm : ∀ p q → (p ∧ᵒ q) ≈ᵍ (q ∧ᵒ p)
  ∧ᵒ-comm (inj₁ x) (inj₁ y) = ∧₁-comm x y , refl₂
  ∧ᵒ-comm (inj₁ x) (inj₂ y) = refl₁ , refl₂
  ∧ᵒ-comm (inj₂ x) (inj₁ y) = refl₁ , refl₂
  ∧ᵒ-comm (inj₂ x) (inj₂ y) = refl₁ , ∧₂-comm x y

  ∧ᵒ-idem : ∀ p → (p ∧ᵒ p) ≈ᵍ p
  ∧ᵒ-idem (inj₁ x) = ∧₁-idem x , refl₂
  ∧ᵒ-idem (inj₂ x) = refl₁ , ∧₂-idem x

  ∨ᵒ-assoc : ∀ p q r → ((p ∨ᵒ q) ∨ᵒ r) ≈ᵍ (p ∨ᵒ (q ∨ᵒ r))
  ∨ᵒ-assoc (inj₁ x) (inj₁ y) (inj₁ z) = ∨₁-assoc x y z , refl₂
  ∨ᵒ-assoc (inj₁ x) (inj₁ y) (inj₂ z) = refl₁ , refl₂
  ∨ᵒ-assoc (inj₁ x) (inj₂ y) (inj₁ z) = refl₁ , refl₂
  ∨ᵒ-assoc (inj₁ x) (inj₂ y) (inj₂ z) = refl₁ , refl₂
  ∨ᵒ-assoc (inj₂ x) (inj₁ y) (inj₁ z) = refl₁ , refl₂
  ∨ᵒ-assoc (inj₂ x) (inj₁ y) (inj₂ z) = refl₁ , refl₂
  ∨ᵒ-assoc (inj₂ x) (inj₂ y) (inj₁ z) = refl₁ , refl₂
  ∨ᵒ-assoc (inj₂ x) (inj₂ y) (inj₂ z) = refl₁ , ∨₂-assoc x y z

  ∨ᵒ-comm : ∀ p q → (p ∨ᵒ q) ≈ᵍ (q ∨ᵒ p)
  ∨ᵒ-comm (inj₁ x) (inj₁ y) = ∨₁-comm x y , refl₂
  ∨ᵒ-comm (inj₁ x) (inj₂ y) = refl₁ , refl₂
  ∨ᵒ-comm (inj₂ x) (inj₁ y) = refl₁ , refl₂
  ∨ᵒ-comm (inj₂ x) (inj₂ y) = refl₁ , ∨₂-comm x y

  ∨ᵒ-idem : ∀ p → (p ∨ᵒ p) ≈ᵍ p
  ∨ᵒ-idem (inj₁ x) = ∨₁-idem x , refl₂
  ∨ᵒ-idem (inj₂ x) = refl₁ , ∨₂-idem x

  absorbˡᵒ : ∀ p q → (p ∧ᵒ (p ∨ᵒ q)) ≈ᵍ p
  absorbˡᵒ (inj₁ x) (inj₁ y) = absorbˡ₁ x y , refl₂
  absorbˡᵒ (inj₁ x) (inj₂ y) = refl₁ , refl₂
  absorbˡᵒ (inj₂ x) (inj₁ y) = refl₁ , ∧₂-idem x
  absorbˡᵒ (inj₂ x) (inj₂ y) = refl₁ , absorbˡ₂ x y

  absorbʳᵒ : ∀ p q → ((p ∧ᵒ q) ∨ᵒ p) ≈ᵍ p
  absorbʳᵒ (inj₁ x) (inj₁ y) = absorbʳ₁ x y , refl₂
  absorbʳᵒ (inj₁ x) (inj₂ y) = ∨₁-idem x , refl₂
  absorbʳᵒ (inj₂ x) (inj₁ y) = refl₁ , refl₂
  absorbʳᵒ (inj₂ x) (inj₂ y) = refl₁ , absorbʳ₂ x y
```

Assembling through the setoid-level builder yields the ordinal sum.  (The two
congruence arguments are η-expanded with their implicits forwarded: the carrier
`A ⊎ B` has no η-rule, so Agda cannot recover the endpoints of an under-applied
congruence through the non-injective retractions.)

```agda
  ⊕-Lattice : Lattice (α ⊔ β) (ρ ⊔ σ)
  ⊕-Lattice = setoidEqsToLattice glueSetoid _∧ᵒ_ _∨ᵒ_
    (λ {p} {q} {u} {v} → ∧ᵒ-cong {p} {q} {u} {v})
    (λ {p} {q} {u} {v} → ∨ᵒ-cong {p} {q} {u} {v})
    ∧ᵒ-assoc ∧ᵒ-comm ∧ᵒ-idem ∨ᵒ-assoc ∨ᵒ-comm ∨ᵒ-idem absorbˡᵒ absorbʳᵒ
```

#### The sum order, characterized

The meet order of the sum unfolds definitionally on each constructor
combination: within a summand it is that summand's order, everything low is below
everything high, and the only way an upper element sits below a lower one is at
the glue.  The four lemmas name these unfoldings for consumers.

```agda
  open Lattice-Order ⊕-Lattice using () renaming ( _≤_ to _≤ᵒ_ )

  -- Within the lower summand, the sum order is the lower order.
  ≤ᵒ-inj₁ : {x y : 𝕌[ 𝑨 ]} → x ≤₁ y → (inj₁ x) ≤ᵒ (inj₁ y)
  ≤ᵒ-inj₁ e = e , refl₂

  ≤ᵒ-inj₁-elim : {x y : 𝕌[ 𝑨 ]} → (inj₁ x) ≤ᵒ (inj₁ y) → x ≤₁ y
  ≤ᵒ-inj₁-elim = proj₁

  -- Within the upper summand, the sum order is the upper order.
  ≤ᵒ-inj₂ : {x y : 𝕌[ 𝑩 ]} → x ≤₂ y → (inj₂ x) ≤ᵒ (inj₂ y)
  ≤ᵒ-inj₂ e = refl₁ , e

  ≤ᵒ-inj₂-elim : {x y : 𝕌[ 𝑩 ]} → (inj₂ x) ≤ᵒ (inj₂ y) → x ≤₂ y
  ≤ᵒ-inj₂-elim = proj₂

  -- Everything in the lower summand is below everything in the upper one.
  ≤ᵒ-up : (x : 𝕌[ 𝑨 ]) (y : 𝕌[ 𝑩 ]) → (inj₁ x) ≤ᵒ (inj₂ y)
  ≤ᵒ-up x y = refl₁ , refl₂

  -- An upper element below a lower one forces both to the glue.
  ≤ᵒ-down-elim : {x : 𝕌[ 𝑩 ]} {y : 𝕌[ 𝑨 ]}
    → (inj₂ x) ≤ᵒ (inj₁ y) → (y ≈₁ ⊤₁) × (x ≈₂ ⊥₂)
  ≤ᵒ-down-elim (p , q) = p , sym₂ q
```

#### The sum operator

The standalone operator, for consumers that need only the lattice.

```agda
ordinalSum : (𝑳₁ : Lattice α ρ) → TopOf 𝑳₁ → (𝑳₂ : Lattice β σ) → BotOf 𝑳₂
  → Lattice (α ⊔ β) (ρ ⊔ σ)
ordinalSum 𝑳₁ t 𝑳₂ b = LatticeOrdinalSum.⊕-Lattice 𝑳₁ t 𝑳₂ b
```

--------------------------------------
