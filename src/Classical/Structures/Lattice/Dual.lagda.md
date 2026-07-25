---
layout: default
file: "src/Classical/Structures/Lattice/Dual.lagda.md"
title: "Classical.Structures.Lattice.Dual module"
date: "2026-07-24"
author: "the agda-algebras development team"
---

### The dual of a lattice {#classical-structures-lattice-dual}

This is the [Classical.Structures.Lattice.Dual][] module of the [Agda Universal Algebra Library][].

The **dual** (or *opposite*) of a lattice swaps meet and join, equivalently reverses
the order.  Because the lattice theory `Th-Lattice` is self-dual, the construction is
a matter of re-interpreting the two operation symbols of
[`Sig-Lattice`][Classical.Signatures.Lattice] on the *same* carrier setoid: the
dual's meet is `𝑳`{.AgdaBound}'s join and vice versa, six of the eight equations
transfer verbatim with the `∧`/`∨` roles exchanged, and the two absorption laws
of the dual follow from those of `𝑳`{.AgdaBound} by one commutativity step each
(`a ∨ (a ∧ b) ≈ a` is `absorbʳ`{.AgdaFunction} read backwards).

The module also records how the dualization acts on the derived order-theoretic data
of [Classical.Properties.Lattice][].

+  The meet order flips: `x ≤ y` in the dual iff `y ≤ x` in `𝑳`{.AgdaBound}
   (`≤ᵈ-flip`{.AgdaFunction} / `≤ᵈ-unflip`{.AgdaFunction}).
+  Chosen extrema swap: a top of `𝑳`{.AgdaBound} is a bottom of the dual and
   conversely (`dualBotOf`{.AgdaFunction} / `dualTopOf`{.AgdaFunction}).

Dualization is involutive up to the evident isomorphism (the identity map on the
carrier): applying `dualLattice`{.AgdaFunction} twice re-interprets each symbol by
its original operation, pointwise.  We do not formalize the involution here — as a
propositional equality of `Lattice`{.AgdaFunction} values it would need function
extensionality — and no current consumer requires it; a consumer that dualizes
twice should transport along the identity carrier map.

The first consumer is the Kurzweil–Netter duality entry of the FLRP assumptions
registry: the classical theorem that the
class of representable lattices is closed under dualization is *stated* over
`dualLattice`{.AgdaFunction} and imported as an explicit hypothesis.[^1]

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Lattice.Dual where


-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Product          using ( _,_ ; proj₁ )
open import Level                 using ( Level )
open import Relation.Binary       using ( Setoid )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice  using ( module Lattice-Order ; TopOf ; BotOf )
open import Classical.Structures.Lattice  using ( Lattice ; module Lattice-Op
                                                ; setoidEqsToLattice )
open import Setoid.Algebras.Basic         using ( 𝔻[_] )

private variable α ρ : Level
```
-->

#### The dual construction

`LatticeDual`{.AgdaModule} `𝑳` packages the construction and its order-theoretic
companions for a fixed lattice.

```agda
module LatticeDual (𝑳 : Lattice α ρ) where
  private 𝑨 = proj₁ 𝑳

  open Setoid 𝔻[ 𝑨 ] using ( _≈_ )
    renaming ( trans to ≈trans )
  open Lattice-Op 𝑳 using
    ( _∧_ ; _∨_ ; ∧-cong ; ∨-cong
    ; ∧-assoc-law ; ∧-comm-law ; ∧-idem-law
    ; ∨-assoc-law ; ∨-comm-law ; ∨-idem-law
    ; absorbˡ-law ; absorbʳ-law )
```

The two absorption laws of the dual, derived from those of `𝑳` by one
commutativity step each.

```agda
  -- a ∨ (a ∧ b) ≈ a : the dual reading of absorption, from absorbʳ by ∨-commutativity.
  dual-absorbˡ : ∀ a b → (a ∨ (a ∧ b)) ≈ a
  dual-absorbˡ a b = ≈trans ∨-comm-law absorbʳ-law

  -- (a ∨ b) ∧ a ≈ a : the other dual absorption, from absorbˡ by ∧-commutativity.
  dual-absorbʳ : ∀ a b → ((a ∨ b) ∧ a) ≈ a
  dual-absorbʳ a b = ≈trans ∧-comm-law absorbˡ-law
```

The dual lattice: same carrier setoid, meet interpreted by `_∨_` and join by
`_∧_`, the six semilattice equations exchanged wholesale, and the two derived
absorption laws.

```agda
  dual-Lattice : Lattice α ρ
  dual-Lattice = setoidEqsToLattice 𝔻[ 𝑨 ] _∨_ _∧_ ∨-cong ∧-cong
    (λ x y z → ∨-assoc-law{x}{y}{z})
    (λ x y → ∨-comm-law {x}{y})
    (λ x → ∨-idem-law{x})
    (λ x y z → ∧-assoc-law {x}{y}{z})
    (λ x y → ∧-comm-law {x}{y})
    (λ x → ∧-idem-law{x})
    dual-absorbˡ dual-absorbʳ
```

#### The dual order is the reversed order

The meet order of the dual unfolds definitionally to `x ∨ y ≈ x`, which is the
join-form characterization of `y ≤ x` in `𝑳` ([Classical.Properties.Lattice][]'s
connecting lemmas); the two directions are one commutativity step each.

```agda
  open Lattice-Order 𝑳 using ( ≤-via-∨ ; ≤-from-∨ ) renaming ( _≤_ to _≤₀_ )
  open Lattice-Order dual-Lattice using () renaming ( _≤_ to _≤ᵈ_ )

  -- An inequality in the dual reverses in 𝑳.
  ≤ᵈ-flip : ∀ {x y} → x ≤ᵈ y → y ≤₀ x
  ≤ᵈ-flip {x} {y} x≤ᵈy = ≤-from-∨ (≈trans ∨-comm-law x≤ᵈy)

  -- An inequality in 𝑳 reverses in the dual.
  ≤ᵈ-unflip : ∀ {x y} → y ≤₀ x → x ≤ᵈ y
  ≤ᵈ-unflip {x} {y} y≤x = ≈trans ∨-comm-law (≤-via-∨ y≤x)
```

#### Extrema swap under dualization

A chosen top of `𝑳` is a chosen bottom of the dual, and conversely — the element
is unchanged, and its universal property flips through
`≤ᵈ-unflip`{.AgdaFunction}.

```agda
  dualBotOf : TopOf 𝑳 → BotOf dual-Lattice
  dualBotOf (t , t-top) = t , λ x → ≤ᵈ-unflip (t-top x)

  dualTopOf : BotOf 𝑳 → TopOf dual-Lattice
  dualTopOf (b , b-bot) = b , λ x → ≤ᵈ-unflip (b-bot x)
```

#### The dual operator

The standalone operator, for consumers that need only the lattice.

```agda
dualLattice : Lattice α ρ → Lattice α ρ
dualLattice 𝑳 = LatticeDual.dual-Lattice 𝑳
```

--------------------------------------
[^1]: See [FLRP.Assumptions][] and work package WP-5.
