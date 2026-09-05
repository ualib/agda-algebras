---
layout: default
file: "src/Classical/Structures/Lattice/Parachute.lagda.md"
title: "Classical.Structures.Lattice.Parachute module"
date: "2026-07-25"
author: "the agda-algebras development team"
---

### Parachute lattices {#classical-structures-lattice-parachute}

This is the [Classical.Structures.Lattice.Parachute][] module of the [Agda Universal Algebra Library][].

The **parachute lattice** `𝒫 = 𝒫(L₁, … , Lₙ)` of a finite family of lattices is a
fresh bottom element together with `n` **canopies** `Lᵢ`, sitting side-by-side and
connected by a single shared top.  Distinct canopies meet at the bottom and join at the top,
and inside a canopy the order is that canopy's own.  The bottoms `⊥ᵢ` of the
canopies are the `n` atoms of `𝒫`, and the interval above the `i`-th atom is
`Lᵢ`.

The parachute lattice was first described in the note
[Interval enforceable properties of finite groups](https://arxiv.org/abs/1205.1927v4) (2012),
which we will call "the note" in this module.[^1]

The parachute construction is the engine of the note's Theorem 3.6 and Lemma 3.7:
a core-free group representation of a parachute forces every proper subgroup above
an atom to be core-free, so the enforceable properties of all the canopies must
hold of a single group.

??? note "**Design Note**: normal forms rather than gluing"

    A first instinct is to build the carrier as a disjoint union `⊥ + Σᵢ Lᵢ` with the
    setoid equality coarsened to identify the `n` tops, in the style of
    `GlueSetoid`{.AgdaModule} of [Classical.Structures.Lattice.OrdinalSum][].
    That fails constructively and instructively: with the tops glued, the meet of
    `inj (i , x)` and `inj (j , y)` for `i ≠ j` must be the bottom when `x` and `y`
    are proper canopy elements and must be `inj (j , y)` when `x` is the top;
    deciding between the two is deciding `x ≈ ⊤ᵢ`.  No congruent meet exists without
    that decision.

We define a *normal form* for the carrier: the top, the bottom, and the proper
elements of each canopy, tagged with their canopy index.  No explicit quotient
type is defined and the order is a three-constructor inductive family.  This
decision reappears exactly once, in the join of two elements of the same canopy
(which may reach the top), and is supplied as the module parameter
`top?`.[^2]

The order `_≤ᵖ_`{.AgdaFunction} is an *inductive family indexed by its endpoints*.
The dividend here is that the order constructor `c≤c`{.AgdaFunction} carries the
canopy index *once*: matching a proof that two canopy elements are comparable
identifies their canopies with no appeal to decidable index equality.[^3]

Equality is then *mutual comparability*, `u ≈ᵖ v = (u ≤ᵖ v) × (v ≤ᵖ u)` — the
order-theoretic equality the subuniverse lattice of [Setoid.Subalgebras.CompleteLattice][]
also uses.  This is not a stylistic choice.  Because the canopy carrier `U i`
*depends* on the index, inverting a proof about two elements of a canopy that
Agda already knows to be the same canopy would need to eliminate the reflexive
equation `i ≡ i`, which `--without-K` forbids; with equality defined as mutual
comparability, antisymmetry is the pairing function and no such inversion is ever
required.  (The head of the definition is `_×_`, which has η, and its two
components are applications of the injective family `_≤ᵖ_`, so the inference hazard
issue #504 documents does not arise.)

??? note "**Design Note**: the order comes first"

    The eight lattice equations — in particular the two congruences, which is where
    the ordinal sum spends most of its length — are not proved by hand.  We establish
    instead that `_≤ᵖ_`{.AgdaFunction} is a partial order with `_∧ᵖ_`{.AgdaFunction}
    its infimum and `_∨ᵖ_`{.AgdaFunction} its supremum, and let the standard
    library's `Relation.Binary.Lattice.Properties.Lattice` derive the algebraic laws.
    Congruence of the operations is then a *theorem* (an infimum is unique up to
    `≈`), not an obligation, and the case analyses stay small.

??? note "**Design Note**: every case split is a named lemma**

    Each of the three decisions the construction makes — is this canopy element the
    top, do these two elements share a canopy, and (on the diagonal) the comparison
    of an index with itself — is analysed in one small `private` lemma taking the
    `Dec`{.AgdaDatatype} value as an explicit argument, and every consumer applies
    that lemma instead of repeating the split.

    Besides being the library's house style, this is what keeps the module cheap to
    type-check: a `with` inside a proof abstracts the *whole* goal, and these goals
    mention the canopy order, which unfolds into the generic interpretation machinery
    of `Algebra`{.AgdaRecord}.  Pushing the split into a lemma with a small goal
    removed about two thirds of the module's coverage-checking cost.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Lattice.Parachute where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥-elim )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F )
open import Data.Fin.Properties                    using ( _≟_ )
open import Data.Nat.Base                          using ( ℕ ; suc )
open import Data.Product                           using ( _,_ ; _×_ ; Σ-syntax
                                                         ; proj₁ ; proj₂ ; swap )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ )
open import Level                                  using ( Level ; _⊔_ )
                                                   renaming ( suc to lsuc )
open import Relation.Binary                        using ( Setoid ; IsEquivalence
                                                         ; IsPartialOrder )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; ≡-≟-identity )
open import Relation.Nullary                       using ( ¬_ ; Dec ; yes ; no )

import Algebra.Lattice                             as AlgLattice
import Relation.Binary.Lattice                     as OrdLattice
import Relation.Binary.Lattice.Properties.Lattice  as OrdLatticeProps

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice        using  ( module Lattice-Order
                                                       ; TopOf ; BottomOf )
open import Classical.Structures.Lattice.Basic  using  ( Lattice ; module Lattice-Op
                                                       ; setoidEqsToLattice )
open import Setoid.Algebras.Basic               using  ( 𝕌[_] ; 𝔻[_] )

private variable α ρ : Level
```
-->

#### The data of a parachute

A `Parachute α ρ m`{.AgdaRecord} is the data the construction consumes: `suc m`
canopies `𝓛`, their chosen tops `𝒕` (all identified in the parachute), the decision
procedure `top?` for being the top of one's canopy, their chosen bottoms `𝒃` (the
atoms of the parachute), and the assumption `nondeg` that no canopy is a single
point (without which its "atom" would be its top).  The canopy index is implicit
in `𝒕`, `top?`, and `𝒃`, where the element determines it, and explicit in `nondeg`,
where nothing else does.

There is at least one canopy: a parachute over the empty family has no atoms below
its bottom, and the covering property below would fail.

```agda
record Parachute (α ρ : Level) (m : ℕ) : Type (lsuc (α ⊔ ρ)) where
  field
    𝓛       : Fin (suc m) → Lattice α ρ
    𝒕       : ∀ {i} → TopOf (𝓛 i)
    top?    : ∀ {i} (x : 𝕌[ 𝓛 i .proj₁ ]) → Dec (Setoid._≈_ 𝔻[ 𝓛 i .proj₁ ] x (𝒕 .proj₁))
    𝒃       : ∀ {i} → BottomOf (𝓛 i)
    nondeg  : ∀ i → ¬ Setoid._≈_ 𝔻[ 𝓛 i .proj₁ ] (𝒃 .proj₁) (𝒕 .proj₁)
```

#### The construction

`LatticeParachute 𝒫` builds the parachute lattice of `𝒫`.  Its body refers to the
five fields by name and re-exports them, so that a consumer that opens the module
sees the canopies `𝓛 i` alongside what is built from them.

```agda
module LatticeParachute {m : ℕ} (𝒫 : Parachute α ρ m) where

  open Parachute 𝒫 public

  -- The canopy index.
  Ix : Type
  Ix = Fin (suc m)
```

Per-canopy notation.  The carriers `U i` are the images of a function of `i`, so
inside the anonymous module below the canopy index is an implicit parameter that
Agda reads off the elements: for `x y : U i`, `x ≈ y` and `x ≤ y` are that
canopy's equality and order, with no index written.

```agda
  -- The carrier of the i-th canopy.
  U : Ix → Type α
  U i = 𝕌[ 𝓛 i .proj₁ ]

  module _ {i : Ix} where

    -- Equality and order inside a canopy.
    _≈_ : U i → U i → Type ρ
    _≈_ = Setoid._≈_ 𝔻[ 𝓛 i .proj₁ ]

    _≤_ : U i → U i → Type ρ
    _≤_ = Lattice-Order._≤_ (𝓛 i)
    infix 4 _≈_ _≤_

    -- Meet, join, and the two chosen ends of a canopy.
    _⋀_ : U i → U i → U i
    _⋀_ = Lattice-Op._∧_ (𝓛 i)
    _⋁_ : U i → U i → U i
    _⋁_ = Lattice-Op._∨_ (𝓛 i)
    infixl 7 _⋀_ _⋁_

    top : U i
    top = 𝒕 .proj₁

    bot : U i
    bot = 𝒃 .proj₁
```

<!--
```agda
    ≈refl : {x : U i} → x ≈ x
    ≈refl = Setoid.refl 𝔻[ 𝓛 i .proj₁ ]

    ≈sym : {x y : U i} → x ≈ y → y ≈ x
    ≈sym = Setoid.sym 𝔻[ 𝓛 i .proj₁ ]

    ≈trans : {x y z : U i} → x ≈ y → y ≈ z → x ≈ z
    ≈trans = Setoid.trans 𝔻[ 𝓛 i .proj₁ ]

    ≤refl : {x : U i} → x ≤ x
    ≤refl = Lattice-Order.≤-refl (𝓛 i)

    ≤reflexive : {x y : U i} → x ≈ y → x ≤ y
    ≤reflexive = Lattice-Order.≤-reflexive (𝓛 i)

    ≤trans : {x y z : U i} → x ≤ y → y ≤ z → x ≤ z
    ≤trans = Lattice-Order.≤-trans (𝓛 i)

    ≤antisym : {x y : U i} → x ≤ y → y ≤ x → x ≈ y
    ≤antisym = Lattice-Order.≤-antisym (𝓛 i)

    ∧lowerˡ : {x y : U i} → x ⋀ y ≤ x
    ∧lowerˡ = Lattice-Order.∧-lowerˡ (𝓛 i)

    ∧lowerʳ : {x y : U i} → x ⋀ y ≤ y
    ∧lowerʳ = Lattice-Order.∧-lowerʳ (𝓛 i)

    ∧greatest : {x y z : U i} → z ≤ x → z ≤ y → z ≤ x ⋀ y
    ∧greatest = Lattice-Order.∧-greatest (𝓛 i)

    ∨upperˡ : {x y : U i} → x ≤ x ⋁ y
    ∨upperˡ = Lattice-Order.∨-upperˡ (𝓛 i)

    ∨upperʳ : {x y : U i} → y ≤ x ⋁ y
    ∨upperʳ = Lattice-Order.∨-upperʳ (𝓛 i)

    ∨least : {x y z : U i} → x ≤ z → y ≤ z → x ⋁ y ≤ z
    ∨least = Lattice-Order.∨-least (𝓛 i)

    ≤top : (x : U i) → x ≤ top
    ≤top = 𝒕 .proj₂

    ≤bot : (x : U i) → bot ≤ x
    ≤bot = 𝒃 .proj₂
```
-->

An element of a canopy is **proper** when it is not that canopy's top; the proper
elements are the ones the parachute keeps separate.

```agda
    -- x is not the top of canopy i.
    NonTop : U i → Type ρ
    NonTop x = ¬ (x ≈ top)

    -- Meets inherit properness: if x ⋀ y were the top then so would x be.
    meet-NonTop : {x y : U i} → NonTop x → NonTop (x ⋀ y)
    meet-NonTop {x = x} p x∧y≈⊤ =
      p (≤antisym (≤top x) (≤trans (≤reflexive (≈sym x∧y≈⊤)) ∧lowerˡ ))
```

The carrier: the shared top, the fresh bottom, and the proper elements of the
canopies, each tagged with its index.

```agda
  data P : Type (α ⊔ ρ) where
    ⊤ᵖ   : P
    ⊥ᵖ   : P
    can  : {i : Ix} (x : U i) → NonTop x → P
```

Equality and order are inductive families indexed by their endpoints.  Two proper
canopy elements are related only within a common canopy, and the *proof* records
that canopy once, so matching on a proof identifies the two indices.

```agda
  infix 4 _≈ᵖ_ _≤ᵖ_

  data _≤ᵖ_ : P → P → Type (α ⊔ ρ) where
    ⊥-least  : {z : P} → ⊥ᵖ ≤ᵖ z
    ⊤-great  : {z : P} → z ≤ᵖ ⊤ᵖ
    c≤c      : {i : Ix} {x y : U i} {p : NonTop x} {q : NonTop y}
               → x ≤ y → can x p ≤ᵖ can y q

  -- Equality is mutual comparability; see the discussion above.
  _≈ᵖ_ : P → P → Type (α ⊔ ρ)
  u ≈ᵖ v = u ≤ᵖ v × v ≤ᵖ u
```

`_≤ᵖ_`{.AgdaFunction} is a partial order: reflexivity and transitivity split on the
elements and on the proofs respectively, the cases that cross constructors being
impossible by injectivity, and antisymmetry is the pairing function.

```agda
  ≤ᵖ-refl : {z : P} → z ≤ᵖ z
  ≤ᵖ-refl {⊤ᵖ} = ⊤-great
  ≤ᵖ-refl {⊥ᵖ} = ⊥-least
  ≤ᵖ-refl {can _ _} = c≤c ≤refl

  ≤ᵖ-trans : {u v w : P} → u ≤ᵖ v → v ≤ᵖ w → u ≤ᵖ w
  ≤ᵖ-trans ⊥-least ⊥-least = ⊥-least
  ≤ᵖ-trans ⊥-least ⊤-great = ⊥-least
  ≤ᵖ-trans ⊥-least (c≤c _) = ⊥-least
  ≤ᵖ-trans ⊤-great ⊤-great = ⊤-great
  ≤ᵖ-trans (c≤c _) ⊤-great = ⊤-great
  ≤ᵖ-trans (c≤c {i} e) (c≤c f) = c≤c (≤trans e f)

  ≤ᵖ-antisym : {z w : P} → z ≤ᵖ w → w ≤ᵖ z → z ≈ᵖ w
  ≤ᵖ-antisym z≤w w≤z = z≤w , w≤z

  ≤ᵖ-reflexive : {z w : P} → z ≈ᵖ w → z ≤ᵖ w
  ≤ᵖ-reflexive = proj₁

  ≈ᵖ-refl : {z : P} → z ≈ᵖ z
  ≈ᵖ-refl = ≤ᵖ-refl , ≤ᵖ-refl

  ≈ᵖ-sym : {z w : P} → z ≈ᵖ w → w ≈ᵖ z
  ≈ᵖ-sym = swap

  ≈ᵖ-trans : {u v w : P} → u ≈ᵖ v → v ≈ᵖ w → u ≈ᵖ w
  ≈ᵖ-trans (u≤v , v≤u) (v≤w , w≤v) = ≤ᵖ-trans u≤v v≤w , ≤ᵖ-trans w≤v v≤u

  ≈ᵖ-isEquivalence : IsEquivalence _≈ᵖ_
  ≈ᵖ-isEquivalence = record { refl = ≈ᵖ-refl ; sym = ≈ᵖ-sym ; trans = ≈ᵖ-trans }

  ≤ᵖ-isPartialOrder : IsPartialOrder _≈ᵖ_ _≤ᵖ_
  ≤ᵖ-isPartialOrder = record
    { isPreorder = record  { isEquivalence  = ≈ᵖ-isEquivalence
                           ; reflexive      = ≤ᵖ-reflexive
                           ; trans          = ≤ᵖ-trans
                           }
    ; antisym = ≤ᵖ-antisym
    }
```

#### The three decisions

Each decision the construction makes is analyzed once, in a lemma taking the
`Dec`{.AgdaDatatype} value as an explicit argument.  Everything downstream applies
these lemmas rather than repeating the split.

**Decision 1**.  Is this canopy element the top?

A canopy element `x` *represents* the parachute's top when it is the top of its
canopy, and represents itself otherwise; `↑`{.AgdaFunction}` x` is that element
of `P`{.AgdaFunction}.

```agda
  private
    ↑' : {i : Ix} (x : U i) → Dec (x ≈ top) → P
    ↑' x (yes _) = ⊤ᵖ
    ↑' x (no p) = can x p

  -- The element of the parachute represented by x ∈ Lᵢ.
  ↑ : {i : Ix} → U i → P
  ↑ x = ↑' x (top? x)
```

Five facts about `↑'`{.AgdaFunction}, one for each position in which the decision is
consumed downstream: what sits below it, what it sits below, monotonicity, and its
two values.

```agda
  private

    module _ {i : Ix} where

      -- Below `↑ z`: a proper canopy element sits below it whenever it sits below z.
      ↑'-above : {x z : U i} (p : NonTop x) (d : Dec (z ≈ top))
        → x ≤ z → can x p ≤ᵖ ↑' z d
      ↑'-above p (yes _)  _    = ⊤-great
      ↑'-above p (no _)   x≤z  = c≤c x≤z

      -- Above `↑ z`: it sits below a proper canopy element whenever z does, and
      -- then z was not the top, since nothing but the top lies above the top.
      ↑'-below : {z c : U i} (r : NonTop c) (d : Dec (z ≈ top))
        → z ≤ c → ↑' z d ≤ᵖ can c r
      ↑'-below {c = c} r (yes z≈⊤)  z≤c =
        ⊥-elim (r (≤antisym (≤top c) (≤trans (≤reflexive (≈sym z≈⊤)) z≤c)))
      ↑'-below _ (no _)  z≤c = c≤c z≤c

      -- `↑` is monotone: if x is the canopy top then so is anything above it.
      ↑'-mono : {x y : U i} (d : Dec (x ≈ top)) (e : Dec (y ≈ top))
        → x ≤ y → ↑' x d ≤ᵖ ↑' y e
      ↑'-mono (yes _) (yes _) _ = ⊤-great
      ↑'-mono {y = y} (yes x≈⊤) (no q) x≤y =
        ⊥-elim (q (≤antisym (≤top y) (≤trans (≤reflexive (≈sym x≈⊤)) x≤y)))
      ↑'-mono (no _) (yes _) _ = ⊤-great
      ↑'-mono (no _) (no _) x≤y = c≤c x≤y

      -- `↑` sends the canopy top to the parachute top ...
      ↑'-top : (d : Dec (top {i} ≈ top {i})) → ↑' top d ≈ᵖ ⊤ᵖ
      ↑'-top (yes _) = ≈ᵖ-refl
      ↑'-top (no p) = ⊥-elim (p ≈refl)

      -- ... and a proper canopy element to itself.
      ↑'-can : (x : U i) (p : NonTop x) (d : Dec (x ≈ top)) → ↑' x d ≈ᵖ can x p
      ↑'-can x p (yes q) = ⊥-elim (p q)
      ↑'-can x p (no _) = c≤c ≤refl , c≤c ≤refl
```

The four consequences at the actual decision `top? x`.

```agda
  module _ {i : Ix} where

    ↑-above : {x z : U i} (p : NonTop x) → x ≤ z → can x p ≤ᵖ ↑ z
    ↑-above {z = z} p = ↑'-above p (top? z)

    ↑-below : {z c : U i} (r : NonTop c) → z ≤ c → ↑ z ≤ᵖ can c r
    ↑-below {z} r = ↑'-below r (top? z)

    ↑-mono : {x y : U i} → x ≤ y → ↑ x ≤ᵖ ↑ y
    ↑-mono {x} {y} = ↑'-mono (top? x) (top? y)

    ↑-cong : {x y : U i} → x ≈ y → ↑ x ≈ᵖ ↑ y
    ↑-cong e = ↑-mono (≤reflexive e) , ↑-mono (≤reflexive (≈sym e))

    ↑-top : ↑ (top {i}) ≈ᵖ ⊤ᵖ
    ↑-top = ↑'-top (top? top)

    ↑-can : (x : U i) (p : NonTop x) → ↑ x ≈ᵖ can x p
    ↑-can x p = ↑'-can x p (top? x)
```

**Decision 2: do these two elements share a canopy?**  Meet and join of two proper
elements compare their indices; the join additionally normalizes through
`↑`{.AgdaFunction}, since a canopy join may reach the top.

```agda
  private
    meetᶜ : {i j : Ix} (x : U i) (y : U j) → NonTop x → NonTop y → Dec (i ≡ j) → P
    meetᶜ {i} {.i} x y p _ (yes refl) = can (x ⋀ y) (meet-NonTop p)
    meetᶜ _ _ _ _ (no _) = ⊥ᵖ

    joinᶜ : {i j : Ix} (x : U i) (y : U j) → Dec (i ≡ j) → P
    joinᶜ {i} {.i} x y (yes refl)  = ↑ (x ⋁ y)
    joinᶜ _ _ (no _)      = ⊤ᵖ

  infixr 7 _∧ᵖ_ _∨ᵖ_

  _∧ᵖ_ : P → P → P
  ⊤ᵖ ∧ᵖ z = z
  ⊥ᵖ ∧ᵖ z = ⊥ᵖ
  can x p ∧ᵖ ⊤ᵖ = can x p
  can x p ∧ᵖ ⊥ᵖ = ⊥ᵖ
  can {i} x p ∧ᵖ can {j} y q = meetᶜ x y p q (i ≟ j)

  _∨ᵖ_ : P → P → P
  ⊤ᵖ ∨ᵖ z = ⊤ᵖ
  ⊥ᵖ ∨ᵖ z = z
  can x p ∨ᵖ ⊤ᵖ = ⊤ᵖ
  can x p ∨ᵖ ⊥ᵖ = can x p
  can {i} x p ∨ᵖ can {j} y q   = joinᶜ x y (i ≟ j)
```

What each answer gives, once and for all: within a canopy the operations are that
canopy's, and across canopies they are the two extrema.

```agda
  private
    meetᶜ-lowerˡ : {i j : Ix} (x : U i) (y : U j) (p : NonTop x) (q : NonTop y)
      (d : Dec (i ≡ j)) → meetᶜ x y p q d ≤ᵖ can x p
    meetᶜ-lowerˡ {i} {.i} x y p q (yes refl) = c≤c ∧lowerˡ
    meetᶜ-lowerˡ x y p q (no _) = ⊥-least

    meetᶜ-lowerʳ : {i j : Ix} (x : U i) (y : U j) (p : NonTop x) (q : NonTop y)
      (d : Dec (i ≡ j)) → meetᶜ x y p q d ≤ᵖ can y q
    meetᶜ-lowerʳ {i} {.i} x y p q (yes refl) = c≤c ∧lowerʳ
    meetᶜ-lowerʳ x y p q (no _) = ⊥-least

    joinᶜ-upperˡ : {i j : Ix} (x : U i) (y : U j) (p : NonTop x)
      (d : Dec (i ≡ j)) → can x p ≤ᵖ joinᶜ x y d
    joinᶜ-upperˡ {i} {.i} x y p (yes refl) = ↑-above p ∨upperˡ
    joinᶜ-upperˡ x y p (no _) = ⊤-great

    joinᶜ-upperʳ : {i j : Ix} (x : U i) (y : U j) (q : NonTop y)
      (d : Dec (i ≡ j)) → can y q ≤ᵖ joinᶜ x y d
    joinᶜ-upperʳ {i} {.i} x y q (yes refl) = ↑-above q ∨upperʳ
    joinᶜ-upperʳ x y q (no _) = ⊤-great

    -- Distinct canopies: the meet is the bottom and the join is the top.
    meetᶜ-≢ : {i j : Ix} (x : U i) (y : U j) (p : NonTop x) (q : NonTop y)
      → ¬ i ≡ j → (d : Dec (i ≡ j)) → meetᶜ x y p q d ≤ᵖ ⊥ᵖ
    meetᶜ-≢ x y p q i≢j (yes i≡j)  = ⊥-elim (i≢j i≡j)
    meetᶜ-≢ x y p q i≢j (no _)     = ⊥-least

    joinᶜ-≢ : {i j : Ix} (x : U i) (y : U j)
      → ¬ i ≡ j → (d : Dec (i ≡ j)) → ⊤ᵖ ≤ᵖ joinᶜ x y d
    joinᶜ-≢ x y i≢j (yes i≡j)  = ⊥-elim (i≢j i≡j)
    joinᶜ-≢ x y i≢j (no _)     = ⊤-great
```

**Decision 3: comparing a canopy index with itself**.

When two elements are already known to share a canopy (the case `--without-K`
refuses to match) the comparison still has to be run, and `≟-diag`{.AgdaFunction}
pins its answer.  This is not the K rule: `Fin`{.AgdaDatatype} has decidable
equality, hence unique identity proofs.  The three lemmas below are the only places
it is needed, and each has a small goal.

```agda
  ≟-diag : (i : Ix) → (i ≟ i) ≡ yes refl
  ≟-diag i = ≡-≟-identity _≟_ refl

  private
    -- Two elements of the same canopy meet and join in that canopy.
    ∧ᵖ-diag : (i : Ix) (x y : U i) (p : NonTop x) (q : NonTop y)
      → (can x p ∧ᵖ can y q) ≈ᵖ can (x ⋀ y) (meet-NonTop p)
    ∧ᵖ-diag i x y p q rewrite ≟-diag i = ≈ᵖ-refl

    ∨ᵖ-diag : (i : Ix) (x y : U i) (p : NonTop x) (q : NonTop y)
      → (can x p ∨ᵖ can y q) ≈ᵖ ↑ (x ⋁ y)
    ∨ᵖ-diag i x y p q rewrite ≟-diag i = ≈ᵖ-refl
```

#### Meet is the infimum and join the supremum

Each clause is now an application of one of the lemmas above.

```agda
  ∧ᵖ-lowerˡ : (u v : P) → (u ∧ᵖ v) ≤ᵖ u
  ∧ᵖ-lowerˡ ⊤ᵖ v = ⊤-great
  ∧ᵖ-lowerˡ ⊥ᵖ v = ⊥-least
  ∧ᵖ-lowerˡ (can x p) ⊤ᵖ = ≤ᵖ-refl
  ∧ᵖ-lowerˡ (can x p) ⊥ᵖ = ⊥-least
  ∧ᵖ-lowerˡ (can {i} x p) (can {j} y q) = meetᶜ-lowerˡ x y p q (i ≟ j)

  ∧ᵖ-lowerʳ : (u v : P) → (u ∧ᵖ v) ≤ᵖ v
  ∧ᵖ-lowerʳ ⊤ᵖ v = ≤ᵖ-refl
  ∧ᵖ-lowerʳ ⊥ᵖ v = ⊥-least
  ∧ᵖ-lowerʳ (can x p) ⊤ᵖ = ⊤-great
  ∧ᵖ-lowerʳ (can x p) ⊥ᵖ = ⊥-least
  ∧ᵖ-lowerʳ (can {i} x p) (can {j} y q) = meetᶜ-lowerʳ x y p q (i ≟ j)

  -- Leastness splits on the two order proofs, which read the shared canopy index
  -- off the proofs; only there is the diagonal comparison run.
  ∧ᵖ-greatest : {u v w : P} → w ≤ᵖ u → w ≤ᵖ v → w ≤ᵖ (u ∧ᵖ v)
  ∧ᵖ-greatest ⊥-least _ = ⊥-least
  ∧ᵖ-greatest ⊤-great w≤v = w≤v
  ∧ᵖ-greatest (c≤c e) ⊤-great = c≤c e
  ∧ᵖ-greatest (c≤c {i} {a} {x} {pa} {p} e) (c≤c {y = y} {q = q} f) =
    ≤ᵖ-trans (c≤c (∧greatest e f)) (∧ᵖ-diag i x y p q .proj₂)

  ∨ᵖ-upperˡ : (u v : P) → u ≤ᵖ (u ∨ᵖ v)
  ∨ᵖ-upperˡ ⊤ᵖ v                    = ⊤-great
  ∨ᵖ-upperˡ ⊥ᵖ v                    = ⊥-least
  ∨ᵖ-upperˡ (can  x p) ⊤ᵖ          = ⊤-great
  ∨ᵖ-upperˡ (can  x p) ⊥ᵖ          = ≤ᵖ-refl
  ∨ᵖ-upperˡ (can {i} x p) (can {j} y q) = joinᶜ-upperˡ x y p (i ≟ j)

  ∨ᵖ-upperʳ : (u v : P) → v ≤ᵖ (u ∨ᵖ v)
  ∨ᵖ-upperʳ ⊤ᵖ v                    = ⊤-great
  ∨ᵖ-upperʳ ⊥ᵖ v                    = ≤ᵖ-refl
  ∨ᵖ-upperʳ (can x p) ⊤ᵖ          = ⊤-great
  ∨ᵖ-upperʳ (can x p) ⊥ᵖ          = ⊥-least
  ∨ᵖ-upperʳ (can {i} x p) (can {j} y q) = joinᶜ-upperʳ x y q (i ≟ j)

  ∨ᵖ-least : {u v w : P} → u ≤ᵖ w → v ≤ᵖ w → (u ∨ᵖ v) ≤ᵖ w
  ∨ᵖ-least ⊥-least v≤w      = v≤w
  ∨ᵖ-least ⊤-great _        = ⊤-great
  ∨ᵖ-least (c≤c e) ⊥-least  = c≤c e
  ∨ᵖ-least (c≤c {i} {x} {c} {p} {r} e) (c≤c {x = y} {p = q} f) =
    ≤ᵖ-trans (∨ᵖ-diag i x y p q .proj₁) (↑-below r (∨least e f))
```

#### The parachute as a lattice

Assembling the order-theoretic bundle and handing it to the standard library gives
the algebraic laws; only the two idempotencies are proved here, directly from the
extremum properties.

```agda
  ⊕ᵖ-orderLattice : OrdLattice.Lattice (α ⊔ ρ) (α ⊔ ρ) (α ⊔ ρ)
  ⊕ᵖ-orderLattice = record
    { Carrier    = P
    ; _≈_        = _≈ᵖ_
    ; _≤_        = _≤ᵖ_
    ; _∨_        = _∨ᵖ_
    ; _∧_        = _∧ᵖ_
    ; isLattice  = record
        { isPartialOrder  = ≤ᵖ-isPartialOrder
        ; supremum        = λ u v → ∨ᵖ-upperˡ u v , ∨ᵖ-upperʳ u v , λ _ → ∨ᵖ-least
        ; infimum         = λ u v → ∧ᵖ-lowerˡ u v , ∧ᵖ-lowerʳ u v , λ _ → ∧ᵖ-greatest
        }
    }

  private
    module Alg = AlgLattice.IsLattice (OrdLatticeProps.isAlgLattice ⊕ᵖ-orderLattice)

    ∧ᵖ-idem : {u : P} → (u ∧ᵖ u) ≈ᵖ u
    ∧ᵖ-idem {u} = ∧ᵖ-lowerˡ u u , ∧ᵖ-greatest ≤ᵖ-refl ≤ᵖ-refl

    ∨ᵖ-idem : {u : P} → (u ∨ᵖ u) ≈ᵖ u
    ∨ᵖ-idem {u} = ∨ᵖ-least ≤ᵖ-refl ≤ᵖ-refl , ∨ᵖ-upperˡ u u

  -- The carrier setoid of the parachute.
  parachuteSetoid : Setoid (α ⊔ ρ) (α ⊔ ρ)
  parachuteSetoid = record { Carrier = P ; _≈_ = _≈ᵖ_ ; isEquivalence = ≈ᵖ-isEquivalence }

  -- The parachute lattice 𝒫(L₁ , … , Lₙ).
  ⊕ᵖ-Lattice : Lattice (α ⊔ ρ) (α ⊔ ρ)
  ⊕ᵖ-Lattice = setoidEqsToLattice parachuteSetoid _∧ᵖ_ _∨ᵖ_
    Alg.∧-cong Alg.∨-cong
    (λ {a b c} → Alg.∧-assoc a b c)
    (λ {a b} → Alg.∧-comm a b)
    ∧ᵖ-idem
    (λ {a b c} → Alg.∨-assoc a b c)
    (λ {a b} → Alg.∨-comm a b)
    ∨ᵖ-idem
    (λ {a b} → proj₂ Alg.absorptive a b)
    (λ {a b} → ≈ᵖ-trans (Alg.∨-comm (a ∧ᵖ b) a) (proj₁ Alg.absorptive a b))
```

The lattice's *derived* order — `x ∧ y ≈ x`, the one
[Classical.Properties.Lattice][] computes for every lattice — agrees with the
inductive `_≤ᵖ_`{.AgdaFunction}.  Consumers reason with the inductive family and
transport across with these two lemmas.

```agda
  private module ≤ᴸ = Lattice-Order ⊕ᵖ-Lattice

  -- The inductive order implies the derived one ...
  ≤ᵖ-sound : {u v : P} → u ≤ᵖ v → ≤ᴸ._≤_ u v
  ≤ᵖ-sound {u} {v} u≤v = ∧ᵖ-lowerˡ u v , ∧ᵖ-greatest ≤ᵖ-refl u≤v

  -- ... and conversely.
  ≤ᵖ-complete : {u v : P} → ≤ᴸ._≤_ u v → u ≤ᵖ v
  ≤ᵖ-complete {u} {v} e = ≤ᵖ-trans (proj₂ e) (∧ᵖ-lowerʳ u v)
```

The two extrema, in the packaged form the constructions of
[Classical.Properties.Lattice][] consume.

```agda
  -- (The endpoints are passed explicitly: at the extrema the meet reduces, so
  -- the goal no longer displays the pattern `u ∧ᵖ v` that would determine them.)
  ⊤ᵖ-isTop : TopOf ⊕ᵖ-Lattice
  ⊤ᵖ-isTop = ⊤ᵖ , λ x → ≤ᵖ-sound {x} {⊤ᵖ} ⊤-great

  ⊥ᵖ-isBottom : BottomOf ⊕ᵖ-Lattice
  ⊥ᵖ-isBottom = ⊥ᵖ , λ x → ≤ᵖ-sound {⊥ᵖ} {x} ⊥-least
```

#### Atoms

The bottoms of the canopies are the atoms: `n` of them, one per canopy, meeting at
the bottom and joining at the top, with every element other than the bottom lying
above one of them.

```agda
  -- The bottom of the i-th canopy: an atom of the parachute.
  atom : Ix → P
  atom i = can bot (nondeg i)

  -- Every canopy element lies above its canopy's atom.
  atom-≤ : {i : Ix} (x : U i) (p : NonTop x) → atom i ≤ᵖ can x p
  atom-≤ x p = c≤c (≤bot x)

  -- No atom is the bottom.
  atom-≢⊥ : {i : Ix} → ¬ (atom i ≤ᵖ ⊥ᵖ)
  atom-≢⊥ ()

  -- Distinct atoms meet at the bottom ...
  atoms-meet : (i j : Ix) → ¬ (i ≡ j) → (atom i ∧ᵖ atom j) ≤ᵖ ⊥ᵖ
  atoms-meet i j i≢j = meetᶜ-≢ bot bot (nondeg i) (nondeg j) i≢j (i ≟ j)

  -- ... and join at the top: nothing below the top bounds them both.
  atoms-join : (i j : Ix) → ¬ (i ≡ j) → ⊤ᵖ ≤ᵖ (atom i ∨ᵖ atom j)
  atoms-join i j i≢j = joinᶜ-≢ bot bot i≢j (i ≟ j)

  -- The bottom is covered by the atoms: every other element is above one of them.
  covered : (z : P) → (z ≤ᵖ ⊥ᵖ) ⊎ (Σ[ i ∈ Ix ] (atom i ≤ᵖ z))
  covered ⊥ᵖ = inj₁ ⊥-least
  covered (can {i} x p) = inj₂ (i , atom-≤ x p)
  covered ⊤ᵖ = inj₂ (0F , ⊤-great)

  -- Every element represented by a canopy element lies above that canopy's atom.
  atom-≤-↑ : {i : Ix} (x : U i) → atom i ≤ᵖ ↑ x
  atom-≤-↑ {i} x = ≤ᵖ-trans (↑-can (bot {i}) (nondeg i) .proj₂) (↑-mono (≤bot x))

  -- Being the whole parachute is decidable: only the top is above the top.
  ⊤ᵖ≤? : (z : P) → Dec (⊤ᵖ ≤ᵖ z)
  ⊤ᵖ≤? ⊤ᵖ = yes ⊤-great
  ⊤ᵖ≤? ⊥ᵖ = no λ ()
  ⊤ᵖ≤? (can x p) = no λ ()
```

#### The `i`-th canopy is the interval above the `i`-th atom

The parachute retracts onto each canopy: `π i`{.AgdaFunction} keeps canopy `i`,
sends the shared top to that canopy's top, and collapses everything else to that
canopy's bottom.  Restricted to the elements *above the `i`-th atom* it is inverse
to `↑`{.AgdaFunction}, so the interval `[atom i , ⊤]` of the parachute is
order-isomorphic to `Lᵢ` — the sense in which `Lᵢ` is the `i`-th canopy.  These are
the lemmas the FLRP side transports along an interval isomorphism to read a
representation of `Lᵢ` off a representation of the parachute.

```agda
  private
    πᶜ : {i j : Ix} → U j → Dec (i ≡ j) → U i
    πᶜ {i} {.i} x (yes refl) = x
    πᶜ x (no _) = bot

  -- The retraction onto the i-th canopy.
  π : (i : Ix) → P → U i
  π i ⊤ᵖ = top
  π i ⊥ᵖ = bot
  π i (can {j} x _) = πᶜ x (i ≟ j)

  private
    -- On its own canopy the retraction is the identity (decision 3 again) ...
    πᶜ-diag : {i : Ix} (x : U i) → πᶜ x (i ≟ i) ≈ x
    πᶜ-diag {i} x rewrite ≟-diag i = ≈refl

    -- ... and it is monotone (hence respects the parachute equality).
    πᶜ-mono : {i j : Ix} {x y : U j} (d : Dec (i ≡ j)) → x ≤ y → πᶜ x d ≤ πᶜ y d
    πᶜ-mono (yes refl) e = e
    πᶜ-mono (no _) _ = ≤refl

  π-mono : (i : Ix) {z w : P} → z ≤ᵖ w → π i z ≤ π i w
  π-mono i ⊥-least        = ≤bot _
  π-mono i ⊤-great        = ≤top _
  π-mono i (c≤c {j} e)    = πᶜ-mono (i ≟ j) e

  π-cong : (i : Ix) {z w : P} → z ≈ᵖ w → π i z ≈ π i w
  π-cong i (z≤w , w≤z) = ≤antisym (π-mono i z≤w) (π-mono i w≤z)

  -- The retraction sends the i-th atom to the i-th canopy's bottom.
  π-atom : {i : Ix} → π i (atom i) ≈ bot
  π-atom = πᶜ-diag bot

  -- The two round trips: `π i` and `↑` are mutually inverse between the
  -- canopy `Lᵢ` and the interval above the `i`-th atom.
  private
    π∘↑' : {i : Ix} (x : U i) (d : Dec (x ≈ top)) → π i (↑' x d) ≈ x
    π∘↑' {i} x (yes x≈⊤)  = ≈sym x≈⊤
    π∘↑' {i} x (no _)     = πᶜ-diag x

  π∘↑ : {i : Ix} (x : U i) → π i (↑ x) ≈ x
  π∘↑ x = π∘↑' x (top? x)

  ↑∘π : (i : Ix) (z : P) → atom i ≤ᵖ z → ↑ (π i z) ≈ᵖ z
  ↑∘π i ⊤ᵖ _ = ↑-top
  ↑∘π i (can {.i} x p) (c≤c _) = ≈ᵖ-trans (↑-cong (πᶜ-diag x)) (↑-can x p)
```

#### The lattice a parachute presents

The parachute lattice as a function of its data.  A consumer that wants the
lattice and not the module's vocabulary (a family of lattices indexed by `ℕ`, say)
names it this way.

```agda
-- The parachute lattice 𝒫(L₁ , … , Lₙ) presented by a parachute.
parachuteLattice : {m : ℕ} → Parachute α ρ m → Lattice (α ⊔ ρ) (α ⊔ ρ)
parachuteLattice 𝒫 = LatticeParachute.⊕ᵖ-Lattice 𝒫
```

---

[^1]: See Figure 2 of the FLRP note
      [`docs/papers/flrp/ieprops/IEProps-1205.1927v4.tex`](`docs/papers/flrp/ieprops/IEProps-1205.1927v4.tex),
      § 3.3; see also
      [`docs/notes/flrp-research-roadmap.md`](docs/notes/flrp-research-roadmap.md) § 4
      and the design note [`docs/notes/flrp-rp1-parachutes.md`](docs/notes/flrp-rp1-parachutes.md).

[^2]: This is the [ADR-008][] layer discipline in miniature: the obstruction is
      real, so the decision procedure becomes explicit data rather than the
      construction being weakened.  For the finite lattices over which the FLRP
      quantifies the parameter is free since `Fin`-presented carriers have
      decidable equality.

[^3]: The order is never a relation defined by restriction along a non-injective map.
      Type constructors are injective for unification, so with this approach
      implicit endpoints are resolved before the relation is ever unfolded.  (The
      lesson learned that led to this design decision is described in Issue #504.)
