---
layout: default
file: "src/Classical/Structures/Lattice/Parachute.lagda.md"
title: "Classical.Structures.Lattice.Parachute module"
date: "2026-07-25"
author: "the agda-algebras development team"
---

### Parachute lattices {#classical-structures-lattice-parachute}

This is the [Classical.Structures.Lattice.Parachute][] module of the [Agda Universal Algebra Library][].

The **parachute** `𝒫(L₁, … , Lₙ)` of a finite family of lattices is a fresh bottom
element together with `n` *canopies* `Lᵢ` stacked side by side and glued along a
single shared top: distinct canopies meet at the bottom and join at the top, and
inside a canopy the order is that canopy's own.  When each `Lᵢ` has a bottom `⊥ᵢ`,
those bottoms are the `n` atoms of `𝒫` and the interval above the `i`-th atom is
`Lᵢ` — the picture of Figure 2 of the FLRP note.[^1]

The construction is the engine of the note's Theorem 3.6 and Lemma 3.7: a core-free
group representation of a parachute forces every proper subgroup above an atom to be
core-free, so the enforceable properties of *all* the canopies apply to a single
group.

**Design: normal forms rather than gluing.**  A first instinct is to build the
carrier as a disjoint union `⊥ + Σᵢ Lᵢ` with the setoid equality coarsened to
identify the `n` tops, in the style of `GlueSetoid`{.AgdaModule} of
[Classical.Structures.Lattice.OrdinalSum][].  That fails constructively, and
instructively: with the tops glued, the meet of `inj (i , x)` and `inj (j , y)` for
`i ≠ j` must be the bottom when `x` and `y` are proper canopy elements and must be
`inj (j , y)` when `x` is the top; deciding between the two is deciding `x ≈ ⊤ᵢ`.
No congruent meet exists without that decision.

We therefore give the carrier in **normal form** — the top, the bottom, and the
*proper* elements of each canopy, tagged with their canopy index — so that no
quotient is taken and equality is a three-constructor inductive family.  The
decision reappears exactly once, in the join of two elements of the same canopy
(which may reach the top), and is supplied as the module parameter
`top?`{.AgdaBound}.  This is the [ADR-008][] layer discipline in miniature: the
obstruction is real, so the decision procedure becomes explicit data rather than the
construction being weakened.  For the finite lattices the FLRP quantifies over the
parameter is free — `Fin`-presented carriers have decidable equality.

Per issue #504, the order `_≤ᵖ_`{.AgdaFunction} is an *inductive family indexed by
its endpoints*, never a relation defined by restriction along a non-injective map:
type constructors are injective for unification, so an implicit endpoint is solved
before the relation is ever unfolded.  The dividend here is that the order
constructor `c≤c`{.AgdaFunction} carries the canopy index *once*: matching a proof
that two canopy elements are comparable identifies their canopies with no appeal to
decidable index equality.

Equality is then *mutual comparability*, `u ≈ᵖ v = (u ≤ᵖ v) × (v ≤ᵖ u)` — the
order-theoretic equality the subuniverse lattice of [Setoid.Subalgebras.CompleteLattice][]
also uses.  This is not a stylistic choice.  Because the canopy carrier `U i`
*depends* on the index, inverting a proof about two elements of a canopy that
Agda already knows to be the same canopy would need to eliminate the reflexive
equation `i ≡ i`, which is exactly what `--without-K` forbids; with equality defined
as mutual comparability, antisymmetry is the pairing function and no such inversion
is ever required.  (The head of the definition is `_×_`, which has η, and its two
components are applications of the injective family `_≤ᵖ_`, so the inference hazard
issue #504 documents does not arise.)

**Design: the order comes first.**  The eight lattice equations — in particular the
two congruences, which is where the ordinal sum spends most of its length — are not
proved by hand.  We establish instead that `_≤ᵖ_`{.AgdaFunction} is a partial order
with `_∧ᵖ_`{.AgdaFunction} its infimum and `_∨ᵖ_`{.AgdaFunction} its supremum, and
let the standard library's `Relation.Binary.Lattice.Properties.Lattice` derive the
algebraic laws.  Congruence of the operations is then a *theorem* (an infimum is
unique up to `≈`), not an obligation, and the case analyses stay small.

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
open import Data.Nat.Base                          using ( ℕ )
open import Data.Product                           using ( _,_ ; _×_ ; Σ-syntax
                                                         ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ )
open import Level                                  using ( Level ; _⊔_ )
open import Relation.Binary                        using ( Setoid ; IsEquivalence
                                                         ; IsPartialOrder )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; ≡-≟-identity )
open import Relation.Nullary                       using ( ¬_ ; Dec ; yes ; no )

import Algebra.Lattice                             as AlgLattice
import Relation.Binary.Lattice                     as OrdLattice
import Relation.Binary.Lattice.Properties.Lattice  as OrdLatticeProps

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice  using ( module Lattice-Order ; TopOf ; BotOf )
open import Classical.Structures.Lattice  using ( Lattice ; module Lattice-Op
                                                ; setoidEqsToLattice )
open import Setoid.Algebras.Basic         using ( 𝕌[_] ; 𝔻[_] )

private variable α ρ : Level
```
-->

#### The construction

`LatticeParachute 𝑳 𝒕 top?` fixes the canopies `𝑳`{.AgdaBound}, their chosen tops
`𝒕`{.AgdaBound} (all identified in the parachute), and the decision procedure
`top?`{.AgdaBound} for being the top of one's canopy.

```agda
module LatticeParachute {n : ℕ}
  (𝑳     : Fin n → Lattice α ρ)
  (𝒕     : ∀ i → TopOf (𝑳 i))
  (top?  : ∀ i (x : 𝕌[ proj₁ (𝑳 i) ])
         → Dec (Setoid._≈_ 𝔻[ proj₁ (𝑳 i) ] x (proj₁ (𝒕 i))))
  where
```

Per-canopy notation.  The canopy index is explicit throughout: the carriers `U i`
are the images of a function of `i`, so Agda could not infer it.

```agda
  -- The carrier of the i-th canopy.
  U : Fin n → Type α
  U i = 𝕌[ proj₁ (𝑳 i) ]

  -- Equality and order inside a canopy.
  [_]_≈_ : (i : Fin n) → U i → U i → Type ρ
  [ i ] x ≈ y = Setoid._≈_ 𝔻[ proj₁ (𝑳 i) ] x y

  [_]_≤_ : (i : Fin n) → U i → U i → Type ρ
  [ i ] x ≤ y = Lattice-Order._≤_ (𝑳 i) x y

  -- Meet, join, and the chosen top of a canopy.
  meet : (i : Fin n) → U i → U i → U i
  meet i = Lattice-Op._∧_ (𝑳 i)

  join : (i : Fin n) → U i → U i → U i
  join i = Lattice-Op._∨_ (𝑳 i)

  top : (i : Fin n) → U i
  top i = proj₁ (𝒕 i)
```

<!--
```agda
  private
    ≈refl : (i : Fin n) {x : U i} → [ i ] x ≈ x
    ≈refl i = Setoid.refl 𝔻[ proj₁ (𝑳 i) ]

    ≈sym : (i : Fin n) {x y : U i} → [ i ] x ≈ y → [ i ] y ≈ x
    ≈sym i = Setoid.sym 𝔻[ proj₁ (𝑳 i) ]

    ≈trans : (i : Fin n) {x y z : U i} → [ i ] x ≈ y → [ i ] y ≈ z → [ i ] x ≈ z
    ≈trans i = Setoid.trans 𝔻[ proj₁ (𝑳 i) ]

    ≤refl : (i : Fin n) {x : U i} → [ i ] x ≤ x
    ≤refl i = Lattice-Order.≤-refl (𝑳 i)

    ≤reflexive : (i : Fin n) {x y : U i} → [ i ] x ≈ y → [ i ] x ≤ y
    ≤reflexive i = Lattice-Order.≤-reflexive (𝑳 i)

    ≤trans : (i : Fin n) {x y z : U i} → [ i ] x ≤ y → [ i ] y ≤ z → [ i ] x ≤ z
    ≤trans i = Lattice-Order.≤-trans (𝑳 i)

    ≤antisym : (i : Fin n) {x y : U i} → [ i ] x ≤ y → [ i ] y ≤ x → [ i ] x ≈ y
    ≤antisym i = Lattice-Order.≤-antisym (𝑳 i)

    ∧lowerˡ : (i : Fin n) {x y : U i} → [ i ] meet i x y ≤ x
    ∧lowerˡ i = Lattice-Order.∧-lowerˡ (𝑳 i)

    ∧lowerʳ : (i : Fin n) {x y : U i} → [ i ] meet i x y ≤ y
    ∧lowerʳ i = Lattice-Order.∧-lowerʳ (𝑳 i)

    ∧greatest : (i : Fin n) {x y z : U i} → [ i ] z ≤ x → [ i ] z ≤ y → [ i ] z ≤ meet i x y
    ∧greatest i = Lattice-Order.∧-greatest (𝑳 i)

    ∨upperˡ : (i : Fin n) {x y : U i} → [ i ] x ≤ join i x y
    ∨upperˡ i = Lattice-Order.∨-upperˡ (𝑳 i)

    ∨upperʳ : (i : Fin n) {x y : U i} → [ i ] y ≤ join i x y
    ∨upperʳ i = Lattice-Order.∨-upperʳ (𝑳 i)

    ∨least : (i : Fin n) {x y z : U i} → [ i ] x ≤ z → [ i ] y ≤ z → [ i ] join i x y ≤ z
    ∨least i = Lattice-Order.∨-least (𝑳 i)

    ≤top : (i : Fin n) (x : U i) → [ i ] x ≤ top i
    ≤top i = proj₂ (𝒕 i)
```
-->

An element of a canopy is **proper** when it is not that canopy's top; the proper
elements are the ones the parachute keeps separate.

```agda
  -- x is not the top of canopy i.
  NonTop : (i : Fin n) → U i → Type ρ
  NonTop i x = ¬ ([ i ] x ≈ top i)

  -- Meets inherit properness: if x ∧ y were the top then so would x be.
  meet-NonTop : (i : Fin n) {x y : U i} → NonTop i x → NonTop i (meet i x y)
  meet-NonTop i {x} {y} p x∧y≈⊤ =
    p (≤antisym i (≤top i x) (≤trans i (≤reflexive i (≈sym i x∧y≈⊤)) (∧lowerˡ i)))
```

The carrier: the shared top, the fresh bottom, and the proper elements of the
canopies, each tagged with its index.

```agda
  data P : Type (α ⊔ ρ) where
    ⊤ᵖ   : P
    ⊥ᵖ   : P
    can  : (i : Fin n) (x : U i) → NonTop i x → P
```

Equality and order are inductive families indexed by their endpoints.  Two proper
canopy elements are related only within a common canopy, and the *proof* records
that canopy once — so matching on a proof identifies the two indices.

```agda
  infix 4 _≈ᵖ_ _≤ᵖ_

  data _≤ᵖ_ : P → P → Type (α ⊔ ρ) where
    ⊥-least  : {z : P} → ⊥ᵖ ≤ᵖ z
    ⊤-great  : {z : P} → z ≤ᵖ ⊤ᵖ
    c≤c      : {i : Fin n} {x y : U i} {p : NonTop i x} {q : NonTop i y}
             → [ i ] x ≤ y → can i x p ≤ᵖ can i y q

  -- Equality is mutual comparability; see the discussion above.
  _≈ᵖ_ : P → P → Type (α ⊔ ρ)
  u ≈ᵖ v = (u ≤ᵖ v) × (v ≤ᵖ u)
```

`_≤ᵖ_`{.AgdaFunction} is a partial order: reflexivity and transitivity split on the
elements and on the proofs respectively, the cases that cross constructors being
impossible by injectivity, and antisymmetry is the pairing function.

```agda
  ≤ᵖ-refl : {z : P} → z ≤ᵖ z
  ≤ᵖ-refl {⊤ᵖ}         = ⊤-great
  ≤ᵖ-refl {⊥ᵖ}         = ⊥-least
  ≤ᵖ-refl {can i x p}  = c≤c (≤refl i)

  ≤ᵖ-trans : {u v w : P} → u ≤ᵖ v → v ≤ᵖ w → u ≤ᵖ w
  ≤ᵖ-trans ⊥-least ⊥-least        = ⊥-least
  ≤ᵖ-trans ⊥-least ⊤-great        = ⊥-least
  ≤ᵖ-trans ⊥-least (c≤c _)        = ⊥-least
  ≤ᵖ-trans ⊤-great ⊤-great        = ⊤-great
  ≤ᵖ-trans (c≤c _) ⊤-great        = ⊤-great
  ≤ᵖ-trans (c≤c {i} e) (c≤c f)    = c≤c (≤trans i e f)

  ≤ᵖ-antisym : {z w : P} → z ≤ᵖ w → w ≤ᵖ z → z ≈ᵖ w
  ≤ᵖ-antisym z≤w w≤z = z≤w , w≤z

  ≤ᵖ-reflexive : {z w : P} → z ≈ᵖ w → z ≤ᵖ w
  ≤ᵖ-reflexive = proj₁

  ≈ᵖ-refl : {z : P} → z ≈ᵖ z
  ≈ᵖ-refl = ≤ᵖ-refl , ≤ᵖ-refl

  ≈ᵖ-sym : {z w : P} → z ≈ᵖ w → w ≈ᵖ z
  ≈ᵖ-sym (z≤w , w≤z) = w≤z , z≤w

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

#### The operations

The one place a decision is needed: a canopy element `x` *represents* the top of the
parachute when it is the top of its canopy, and represents itself otherwise.
`↑ i x`{.AgdaFunction} is that element of `P`{.AgdaFunction}.

```agda
  private
    ↑' : (i : Fin n) (x : U i) → Dec ([ i ] x ≈ top i) → P
    ↑' i x (yes _)  = ⊤ᵖ
    ↑' i x (no p)   = can i x p

  -- The element of the parachute represented by x ∈ Lᵢ.
  ↑ : (i : Fin n) → U i → P
  ↑ i x = ↑' i x (top? i x)
```

Meet and join.  Both are decided by cases on the two arguments; the only genuine
computation is between two proper elements, where the canopies are compared and,
for the join, `↑`{.AgdaFunction} normalizes a result that may have reached the top.

```agda
  private
    meetᶜ : (i j : Fin n) (x : U i) (y : U j)
          → NonTop i x → NonTop j y → Dec (i ≡ j) → P
    meetᶜ i .i x y p q (yes refl)  = can i (meet i x y) (meet-NonTop i p)
    meetᶜ i j  x y p q (no _)      = ⊥ᵖ

    joinᶜ : (i j : Fin n) (x : U i) (y : U j) → Dec (i ≡ j) → P
    joinᶜ i .i x y (yes refl)  = ↑ i (join i x y)
    joinᶜ i j  x y (no _)      = ⊤ᵖ

    -- Comparing a canopy index with itself answers yes.  This is *not* the K
    -- rule: `Fin n` has decidable equality, hence unique identity proofs, so
    -- the reflexive case of the comparison is pinned constructively.  It is
    -- needed wherever two elements are already known to share a canopy —
    -- exactly the situation in which `--without-K` refuses to match `refl`.
    ≟-diag : (i : Fin n) → (i ≟ i) ≡ yes refl
    ≟-diag i = ≡-≟-identity _≟_ refl

  infixr 7 _∧ᵖ_
  infixr 6 _∨ᵖ_

  _∧ᵖ_ : P → P → P
  ⊤ᵖ ∧ᵖ z                  = z
  ⊥ᵖ ∧ᵖ z                  = ⊥ᵖ
  can i x p ∧ᵖ ⊤ᵖ          = can i x p
  can i x p ∧ᵖ ⊥ᵖ          = ⊥ᵖ
  can i x p ∧ᵖ can j y q   = meetᶜ i j x y p q (i ≟ j)

  _∨ᵖ_ : P → P → P
  ⊤ᵖ ∨ᵖ z                  = ⊤ᵖ
  ⊥ᵖ ∨ᵖ z                  = z
  can i x p ∨ᵖ ⊤ᵖ          = ⊤ᵖ
  can i x p ∨ᵖ ⊥ᵖ          = can i x p
  can i x p ∨ᵖ can j y q   = joinᶜ i j x y (i ≟ j)
```

Two lemmas about `↑`{.AgdaFunction} isolate its decision: a canopy element sits
below `↑ i z` whenever it sits below `z`, and `↑ i z` sits below a *proper* canopy
element whenever `z` does — in the latter, `z` cannot have been the top, since
nothing but the top lies above the top.

```agda
  private
    ↑-above : (i : Fin n) {x z : U i} (p : NonTop i x) → [ i ] x ≤ z → can i x p ≤ᵖ ↑ i z
    ↑-above i {x} {z} p x≤z with top? i z
    ... | yes _  = ⊤-great
    ... | no _   = c≤c x≤z

    ↑-below : (i : Fin n) {z c : U i} (r : NonTop i c) → [ i ] z ≤ c → ↑ i z ≤ᵖ can i c r
    ↑-below i {z} {c} r z≤c with top? i z
    ... | yes z≈⊤  = ⊥-elim (r (≤antisym i (≤top i c) (≤trans i (≤reflexive i (≈sym i z≈⊤)) z≤c)))
    ... | no _     = c≤c z≤c
```

`_∧ᵖ_`{.AgdaFunction} is the infimum of `_≤ᵖ_`{.AgdaFunction}.  The two lower-bound
clauses split on the arguments; leastness splits on the two order proofs, and the
`c≤c`/`c≤c` case is where the shared canopy index — read off the proofs, not
decided — makes the comparison of indices succeed.

```agda
  ∧ᵖ-lowerˡ : (u v : P) → (u ∧ᵖ v) ≤ᵖ u
  ∧ᵖ-lowerˡ ⊤ᵖ v                    = ⊤-great
  ∧ᵖ-lowerˡ ⊥ᵖ v                    = ⊥-least
  ∧ᵖ-lowerˡ (can i x p) ⊤ᵖ          = ≤ᵖ-refl
  ∧ᵖ-lowerˡ (can i x p) ⊥ᵖ          = ⊥-least
  ∧ᵖ-lowerˡ (can i x p) (can j y q) with i ≟ j
  ... | yes refl  = c≤c (∧lowerˡ i)
  ... | no _      = ⊥-least

  ∧ᵖ-lowerʳ : (u v : P) → (u ∧ᵖ v) ≤ᵖ v
  ∧ᵖ-lowerʳ ⊤ᵖ v                    = ≤ᵖ-refl
  ∧ᵖ-lowerʳ ⊥ᵖ v                    = ⊥-least
  ∧ᵖ-lowerʳ (can i x p) ⊤ᵖ          = ⊤-great
  ∧ᵖ-lowerʳ (can i x p) ⊥ᵖ          = ⊥-least
  ∧ᵖ-lowerʳ (can i x p) (can j y q) with i ≟ j
  ... | yes refl  = c≤c (∧lowerʳ i)
  ... | no _      = ⊥-least

  ∧ᵖ-greatest : {u v w : P} → w ≤ᵖ u → w ≤ᵖ v → w ≤ᵖ (u ∧ᵖ v)
  ∧ᵖ-greatest ⊥-least _        = ⊥-least
  ∧ᵖ-greatest ⊤-great w≤v      = w≤v
  ∧ᵖ-greatest (c≤c e) ⊤-great  = c≤c e
  ∧ᵖ-greatest (c≤c {i} e) (c≤c f) rewrite ≟-diag i = c≤c (∧greatest i e f)
```

Dually for the join.

```agda
  ∨ᵖ-upperˡ : (u v : P) → u ≤ᵖ (u ∨ᵖ v)
  ∨ᵖ-upperˡ ⊤ᵖ v                    = ⊤-great
  ∨ᵖ-upperˡ ⊥ᵖ v                    = ⊥-least
  ∨ᵖ-upperˡ (can i x p) ⊤ᵖ          = ⊤-great
  ∨ᵖ-upperˡ (can i x p) ⊥ᵖ          = ≤ᵖ-refl
  ∨ᵖ-upperˡ (can i x p) (can j y q) with i ≟ j
  ... | yes refl  = ↑-above i p (∨upperˡ i)
  ... | no _      = ⊤-great

  ∨ᵖ-upperʳ : (u v : P) → v ≤ᵖ (u ∨ᵖ v)
  ∨ᵖ-upperʳ ⊤ᵖ v                    = ⊤-great
  ∨ᵖ-upperʳ ⊥ᵖ v                    = ≤ᵖ-refl
  ∨ᵖ-upperʳ (can i x p) ⊤ᵖ          = ⊤-great
  ∨ᵖ-upperʳ (can i x p) ⊥ᵖ          = ⊥-least
  ∨ᵖ-upperʳ (can i x p) (can j y q) with i ≟ j
  ... | yes refl  = ↑-above i q (∨upperʳ i)
  ... | no _      = ⊤-great

  ∨ᵖ-least : {u v w : P} → u ≤ᵖ w → v ≤ᵖ w → (u ∨ᵖ v) ≤ᵖ w
  ∨ᵖ-least ⊥-least v≤w      = v≤w
  ∨ᵖ-least ⊤-great _        = ⊤-great
  ∨ᵖ-least (c≤c e) ⊥-least  = c≤c e
  ∨ᵖ-least (c≤c {i} {q = q} e) (c≤c f) rewrite ≟-diag i = ↑-below i q (∨least i e f)
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

  ⊥ᵖ-isBot : BotOf ⊕ᵖ-Lattice
  ⊥ᵖ-isBot = ⊥ᵖ , λ x → ≤ᵖ-sound {⊥ᵖ} {x} ⊥-least
```

#### Atoms and canopies

With a chosen bottom in each canopy — and the assumption that no canopy is a single
point, without which its "atom" would *be* the top — the parachute acquires the
structure the FLRP argument reads off it: `n` atoms, one per canopy, meeting at the
bottom and joining at the top, with every element other than the bottom lying above
one of them.

```agda
module ParachuteAtoms {m : ℕ}
  (𝑳     : Fin (ℕ.suc m) → Lattice α ρ)
  (𝒕     : ∀ i → TopOf (𝑳 i))
  (top?  : ∀ i (x : 𝕌[ proj₁ (𝑳 i) ])
         → Dec (Setoid._≈_ 𝔻[ proj₁ (𝑳 i) ] x (proj₁ (𝒕 i))))
  (𝒃     : ∀ i → BotOf (𝑳 i))
  (nondeg : ∀ i → ¬ (Setoid._≈_ 𝔻[ proj₁ (𝑳 i) ] (proj₁ (𝒃 i)) (proj₁ (𝒕 i))))
  where

  open LatticeParachute 𝑳 𝒕 top? public

  -- The bottom of the i-th canopy: an atom of the parachute.
  atom : Fin (ℕ.suc m) → P
  atom i = can i (proj₁ (𝒃 i)) (nondeg i)

  -- Every canopy element lies above its canopy's atom.
  atom-≤ : (i : Fin (ℕ.suc m)) (x : U i) (p : NonTop i x) → atom i ≤ᵖ can i x p
  atom-≤ i x p = c≤c (proj₂ (𝒃 i) x)

  -- No atom is the bottom.
  atom-≢⊥ : (i : Fin (ℕ.suc m)) → ¬ (atom i ≤ᵖ ⊥ᵖ)
  atom-≢⊥ i ()

  -- Distinct atoms meet at the bottom.
  atoms-meet : (i j : Fin (ℕ.suc m)) → ¬ (i ≡ j) → (atom i ∧ᵖ atom j) ≤ᵖ ⊥ᵖ
  atoms-meet i j i≢j with i ≟ j
  ... | yes i≡j  = ⊥-elim (i≢j i≡j)
  ... | no _     = ⊥-least

  -- Distinct atoms join at the top: nothing below the top bounds them both.
  atoms-join : (i j : Fin (ℕ.suc m)) → ¬ (i ≡ j) → ⊤ᵖ ≤ᵖ (atom i ∨ᵖ atom j)
  atoms-join i j i≢j with i ≟ j
  ... | yes i≡j  = ⊥-elim (i≢j i≡j)
  ... | no _     = ⊤-great

  -- The bottom is covered by the atoms: every other element is above one of them.
  covered : (z : P) → (z ≤ᵖ ⊥ᵖ) ⊎ (Σ[ i ∈ Fin (ℕ.suc m) ] (atom i ≤ᵖ z))
  covered ⊥ᵖ                = inj₁ ⊥-least
  covered (can i x p)       = inj₂ (i , atom-≤ i x p)
  covered ⊤ᵖ                = inj₂ (0F , ⊤-great)
```

---

[^1]: `docs/papers/flrp/ieprops/IEProps-1205.1927v4.tex`, § 3.3; see also
      [`docs/notes/flrp-research-roadmap.md`](docs/notes/flrp-research-roadmap.md) § 4
      and the design note `docs/notes/flrp-rp1-parachutes.md`.
