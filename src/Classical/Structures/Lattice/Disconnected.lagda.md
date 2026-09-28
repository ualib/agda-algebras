---
layout: default
file: "src/Classical/Structures/Lattice/Disconnected.lagda.md"
title: "Classical.Structures.Lattice.Disconnected module"
date: "2026-09-28"
author: "the agda-algebras development team"
---

### Disconnected lattices: A-lattices, D-lattices, and the parachutes among them {#classical-structures-lattice-disconnected}

This is the [Classical.Structures.Lattice.Disconnected][] module of the
[Agda Universal Algebra Library][].

Aschbacher's program on intervals in subgroup lattices[^1] classifies finite
lattices by the shape of their **proper part**: for a lattice `Λ` with least
element `0` and greatest element `∞`, the proper part is `Λ′ = Λ − {0 , ∞}`,
read as a graph whose adjacency is comparability.  Two of his classes are
defined here, in the vocabulary of [Classical.Properties.Lattice][], together
with the one theorem relating them and the family of examples the FLRP program
cares about.

+  An element `m` is **modular** when `(a ∨ m) ∧ b ≈ a ∨ (m ∧ b)` for all
   `a ≤ b`.  A lattice is an **A-lattice** when it has more than two elements
   and `0` and `∞` are its only modular elements.
+  A lattice is a **D-lattice** when its proper part splits into two parts,
   each a union of connected components (condition (D1)) and each containing a
   nontrivial chain `k < m` (condition (D2)).  D-lattices are the class whose
   minimal representations Aschbacher's Section 6 analyzes; his reduction
   theorem there needs the narrower CD-lattices defined below.  The hexagon is
   the smallest D-lattice.
+  Aschbacher's (1.2): **every D-lattice is an A-lattice**, because an element
   `m` of one part, together with a chain `a < b` of the other part, violates
   modularity: `(a ∨ m) ∧ b = ∞ ∧ b = b` while `a ∨ (m ∧ b) = a ∨ 0 = a`.

The **parachute** `𝒫(L₁ , … , Lₙ)` of [Classical.Structures.Lattice.Parachute][]
is a D-lattice exactly when at least two of its canopies have more than two
elements, which is precisely the hypothesis under which the parachute theorems
of the FLRP program apply.  The proper part of a parachute is the disjoint
union of the canopies with their shared top removed; two proper elements are
comparable only inside a canopy, so the connected components are the canopies
(each connected through its atom), and a canopy carries a nontrivial chain
exactly when it has an element strictly between its atom and the top.
Conversely, a parachute with at most one big canopy is *not* an A-lattice: with
no big canopy every atom is modular, and with exactly one the atom of the big
canopy is.  So for parachutes with at least two canopies, "D-lattice",
"A-lattice", and "at least two big canopies" coincide.

Two of Aschbacher's other classes do **not** contain any parachute with a big
canopy, and the fact is worth recording where the definitions live.  A lattice
is *atomistic* (Aschbacher's `C∗`) when every proper element is a join of atoms,
and *coatomistic* (`C*`) when every proper element is a meet of coatoms; a
*CD-lattice* is a D-lattice that is both.  The atoms of a parachute are the
bottoms of its canopies, one per canopy, and a join of atoms from distinct
canopies is the top, so a proper element of a canopy is a join of atoms only
when it is that canopy's atom.  A parachute with a big canopy is therefore never
atomistic, hence never a CD-lattice, and neither is its dual (which fails the
coatomistic condition by the mirror argument).  The parachutes lie in the class
Aschbacher's *Proposition 2* governs (A-lattices) but outside the class his
*Theorem 3* reduces (CD-lattices); the consequences for the FLRP catalog are
drawn in [FLRP.Reductions][].

**Constructive form**.  Membership in `Λ′` is stated negatively (`¬ (x ≤ 0)`
and `¬ (∞ ≤ x)`), and the A-lattice condition is stated contrapositively, as
"no proper element is modular", which is the form (1.2) proves and every
consumer uses.  The D-lattice data is a two-coloring of the carrier that is
constant across comparable proper pairs; a coloring constant on comparable pairs
is constant on connected components, so this is (D1) without a reachability
relation.  The chosen extrema are parameters, as in `TopOf`{.AgdaFunction} and
`BottomOf`{.AgdaFunction} of [Classical.Properties.Lattice][].

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Lattice.Disconnected where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Bool.Base                         using ( Bool ; true ; false ; not )
open import Data.Empty                             using ( ⊥-elim )
open import Data.Fin.Properties                    using ( _≟_ )
open import Data.Nat.Base                          using ( ℕ )
open import Data.Product                           using ( _,_ ; _×_ ; Σ-syntax
                                                         ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ )
open import Level                                  using ( Level ; _⊔_ )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; trans
                                                         ; cong )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable             using ( does ; dec-true ; dec-false )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice            using  ( module Lattice-Order
                                                           ; TopOf ; BottomOf )
open import Classical.Structures.Lattice.Basic      using  ( Lattice ; module Lattice-Op )
open import Classical.Structures.Lattice.Parachute  using  ( Parachute
                                                           ; module LatticeParachute )
open import Setoid.Algebras.Basic                   using  ( 𝕌[_] ; 𝔻[_] )

private variable α ρ : Level
```
-->

#### Modular elements

The modular law, localized at one element.  A lattice is modular exactly when
every element is modular in this sense; the interest here is in lattices where
almost nothing is.

```agda
module Modular (𝑳 : Lattice α ρ) where
  open Setoid 𝔻[ proj₁ 𝑳 ]  using ( _≈_ )
  open Lattice-Op 𝑳         using ( _∧_ ; _∨_ )
  open Lattice-Order 𝑳      using ( _≤_ )

  -- m is a modular element: (a ∨ m) ∧ b ≈ a ∨ (m ∧ b) whenever a ≤ b.
  IsModularElement : 𝕌[ proj₁ 𝑳 ] → Type (α ⊔ ρ)
  IsModularElement m = ∀ {a b} → a ≤ b → ((a ∨ m) ∧ b) ≈ (a ∨ (m ∧ b))
```

#### A-lattices and D-lattices

Both notions are relative to a chosen bottom and top, which are module
parameters.

```agda
module Disconnected (𝑳 : Lattice α ρ) (⊥ᴸ : BottomOf 𝑳) (⊤ᴸ : TopOf 𝑳) where
  open Setoid 𝔻[ proj₁ 𝑳 ]  using ( _≈_ )
  open Lattice-Op 𝑳         using ( _∧_ ; _∨_ )
  open Lattice-Order 𝑳
  open Modular 𝑳 public

  private
    𝟎 = proj₁ ⊥ᴸ
    𝟏 = proj₁ ⊤ᴸ
    𝟎-min = proj₂ ⊥ᴸ
    𝟏-max = proj₂ ⊤ᴸ
```

A **proper** element lies in `Λ′`: it is neither the bottom nor the top, stated
without deciding either.

```agda
  -- x is neither the bottom nor the top.
  Proper : 𝕌[ proj₁ 𝑳 ] → Type ρ
  Proper x = ¬ (x ≤ 𝟎) × ¬ (𝟏 ≤ x)
```

An **A-lattice**, contrapositively: no proper element is modular.  (Aschbacher
also requires more than two elements; that condition is the separate
three-distinct-elements predicate of the FLRP modules, and it holds in every
instance below, since a D-lattice has at least six elements.)

```agda
  -- No proper element is modular.
  IsALattice : Type (α ⊔ ρ)
  IsALattice = ∀ m → Proper m → ¬ IsModularElement m
```

Comparability is the adjacency of the graph `Λ′`; a **proper chain** is a
nontrivial chain `lo < hi` inside `Λ′`, the witness condition (D2) asks for.

```agda
  -- Adjacency in the comparability graph.
  Comparable : 𝕌[ proj₁ 𝑳 ] → 𝕌[ proj₁ 𝑳 ] → Type ρ
  Comparable x y = (x ≤ y) ⊎ (y ≤ x)

  -- A nontrivial chain of proper elements.
  record ProperChain : Type (α ⊔ ρ) where
    field
      lo hi      : 𝕌[ proj₁ 𝑳 ]
      lo-proper  : Proper lo
      hi-proper  : Proper hi
      lo≤hi      : lo ≤ hi
      hi≰lo      : ¬ (hi ≤ lo)
```

A **D-partition** is Aschbacher's partition `Λ′ = Λ₁ ∪ Λ₂`, as a two-coloring:
comparable proper elements share a color (so each color class is a union of
connected components, condition (D1)), and each color holds a proper chain
(condition (D2)).  A D-lattice is a lattice with a D-partition.

```agda
  record DPartition : Type (α ⊔ ρ) where
    field
      color       : 𝕌[ proj₁ 𝑳 ] → Bool
      -- (D1): a color class is a union of connected components.
      same-color  : ∀ {x y} → Proper x → Proper y → Comparable x y → color x ≡ color y
      -- (D2): each color class contains a nontrivial chain.
      chain       : (c : Bool) → Σ[ k ∈ ProperChain ] color (ProperChain.lo k) ≡ c
```

**Aschbacher's (1.2)**: a D-lattice is an A-lattice.  Fix a proper element `m`
and take the chain `a < b` of the other color.  The meet `m ∧ b` is comparable
to `m` and to `b`, whose colors differ, so it is not proper; being below `b` it
is not the top, so it is the bottom.  Dually `a ∨ m` is the top.  Modularity of
`m` at `a ≤ b` then reads `b = (a ∨ m) ∧ b = a ∨ (m ∧ b) = a`, against
`a < b`.  The two "so it is the bottom / the top" steps are double negations,
and the goal is absurdity, so nothing classical is used.

```agda
  private
    -- The other color, and that it differs.
    not-≡ : (c : Bool) → ¬ (c ≡ not c)
    not-≡ true   ()
    not-≡ false  ()

  D→A : DPartition → IsALattice
  D→A dp m (m≰𝟎 , 𝟏≰m) modular =
    m∧b≤𝟎 λ h₁ → 𝟏≤a∨m λ h₂ → hi≰lo (collapse h₁ h₂)
    where
    open DPartition dp
    open ProperChain (proj₁ (chain (not (color m))))
      renaming ( lo to a ; hi to b )

    m-proper : Proper m
    m-proper = m≰𝟎 , 𝟏≰m

    -- The chain's color is the other one, at both ends.
    a-color : color a ≡ not (color m)
    a-color = proj₂ (chain (not (color m)))

    b-color : color b ≡ not (color m)
    b-color = trans (sym (same-color lo-proper hi-proper (inj₁ lo≤hi))) a-color

    -- m ∧ b is comparable to m and to b, so it cannot be proper ...
    m∧b-not-proper : ¬ Proper (m ∧ b)
    m∧b-not-proper pr = not-≡ (color m)
      (trans (sym (same-color pr m-proper (inj₁ ∧-lowerˡ)))
             (trans (same-color pr hi-proper (inj₁ ∧-lowerʳ)) b-color))

    -- ... and it is not the top, so it is the bottom.
    m∧b≤𝟎 : ¬ ¬ (m ∧ b ≤ 𝟎)
    m∧b≤𝟎 n = m∧b-not-proper (n , λ 𝟏≤m∧b → 𝟏≰m (≤-trans 𝟏≤m∧b ∧-lowerˡ))

    -- Dually, a ∨ m is not proper and not the bottom, so it is the top.
    a∨m-not-proper : ¬ Proper (a ∨ m)
    a∨m-not-proper pr = not-≡ (color m)
      (trans (sym (same-color pr m-proper (inj₂ ∨-upperʳ)))
             (trans (same-color pr lo-proper (inj₂ ∨-upperˡ)) a-color))

    𝟏≤a∨m : ¬ ¬ (𝟏 ≤ a ∨ m)
    𝟏≤a∨m n = a∨m-not-proper ((λ a∨m≤𝟎 → m≰𝟎 (≤-trans ∨-upperʳ a∨m≤𝟎)) , n)

    -- With both ends pinned, modularity at a ≤ b collapses b onto a.
    collapse : m ∧ b ≤ 𝟎 → 𝟏 ≤ a ∨ m → b ≤ a
    collapse h₁ h₂ =
      ≤-trans (≤-respʳ-≈ (modular lo≤hi) (∧-greatest (≤-trans (𝟏-max b) h₂) ≤-refl))
              (∨-least ≤-refl (≤-trans h₁ (𝟎-min a)))
```

#### Parachutes with two big canopies are D-lattices

The coloring is "does this element lie in the canopy `p`": the top and the
bottom are colored arbitrarily, since they are not proper.  Comparable proper
elements of a parachute share a canopy, which the inductive order records in
its one canopy-to-canopy constructor, so (D1) is a match on that proof; the two
chains of (D2) run from the atoms of the two big canopies `p` and `q` to the
elements witnessing their bigness.

```agda
module ParachuteDisconnected {m : ℕ} (𝒫 : Parachute α ρ m) where

  open LatticeParachute 𝒫
  open Disconnected ⊕ᵖ-Lattice ⊥ᵖ-isBottom ⊤ᵖ-isTop public

  -- The derived order of the parachute lattice, for the statements below.
  private module ≤ᴸ = Lattice-Order ⊕ᵖ-Lattice

  -- Comparable proper elements share a canopy.
  sameCanopy : {i j : Ix} {x : U i} {y : U j} {r : NonTop x} {s : NonTop y}
    → can x r ≤ᵖ can y s → i ≡ j
  sameCanopy (c≤c _) = refl

  -- The two extrema are not proper, and every canopy element is.
  private
    can≰⊥ : {i : Ix} {x : U i} {r : NonTop x} → ¬ (can x r ≤ᵖ ⊥ᵖ)
    can≰⊥ ()

    ⊤≰can : {i : Ix} {x : U i} {r : NonTop x} → ¬ (⊤ᵖ ≤ᵖ can x r)
    ⊤≰can ()

  ⊤ᵖ-not-proper : ¬ Proper ⊤ᵖ
  ⊤ᵖ-not-proper (_ , ⊤≰⊤) = ⊤≰⊤ (≤ᵖ-sound {⊤ᵖ} {⊤ᵖ} ⊤-great)

  ⊥ᵖ-not-proper : ¬ Proper ⊥ᵖ
  ⊥ᵖ-not-proper (⊥≰⊥ , _) = ⊥≰⊥ (≤ᵖ-sound {⊥ᵖ} {⊥ᵖ} ⊥-least)

  -- (The endpoints of every order transport below are passed explicitly: at
  -- the extrema the parachute's meet reduces, so the derived order no longer
  -- displays the pattern that would determine them.)
  can-proper : {i : Ix} (x : U i) (r : NonTop x) → Proper (can x r)
  can-proper x r =
    (λ le → can≰⊥ (≤ᵖ-complete {can x r} {⊥ᵖ} le)) , (λ ge → ⊤≰can (≤ᵖ-complete {⊤ᵖ} {can x r} ge))
```

Two big canopies `p ≢ q`, each given by an element strictly between its atom
and the top (the data of `BigCanopyᴸ`{.AgdaRecord} of
[FLRP.Parachute.Representation][], passed field by field).

```agda
  module TwoBig (p q : Ix) (p≢q : ¬ (p ≡ q))
    (xₚ : U p) (xₚ≰bot : ¬ (xₚ ≤ bot)) (xₚ-nonTop : NonTop xₚ)
    (x_q : U q) (x_q≰bot : ¬ (x_q ≤ bot)) (x_q-nonTop : NonTop x_q)
    where

    -- The coloring: is this element in canopy p?
    color : P → Bool
    color ⊤ᵖ            = true
    color ⊥ᵖ            = true
    color (can {i} _ _) = does (i ≟ p)

    -- (D1): comparable proper elements share a canopy, hence a color.
    same-color : ∀ {x y} → Proper x → Proper y → Comparable x y → color x ≡ color y
    same-color {⊤ᵖ}       pr _  _          = ⊥-elim (⊤ᵖ-not-proper pr)
    same-color {⊥ᵖ}       pr _  _          = ⊥-elim (⊥ᵖ-not-proper pr)
    same-color {can _ _}  {⊤ᵖ} _ pr _      = ⊥-elim (⊤ᵖ-not-proper pr)
    same-color {can _ _}  {⊥ᵖ} _ pr _      = ⊥-elim (⊥ᵖ-not-proper pr)
    same-color {can x r}  {can y s} _ _ (inj₁ le) =
      cong (λ k → does (k ≟ p)) (sameCanopy (≤ᵖ-complete {can x r} {can y s} le))
    same-color {can x r}  {can y s} _ _ (inj₂ ge) =
      cong (λ k → does (k ≟ p)) (sym (sameCanopy (≤ᵖ-complete {can y s} {can x r} ge)))
```

The witness element of a big canopy sits strictly above its atom.  Strictness is
read off through the retraction onto the canopy, which is monotone and inverse to
the inclusion there; this avoids inverting an order proof between two elements
already known to share a canopy, which `--cubical-compatible` refuses.

```agda
    private
      -- The chain from the atom of canopy i to a witness of its bigness.
      canopyChain : (i : Ix) (x : U i) → ¬ (x ≤ bot) → (nt : NonTop x) → ProperChain
      canopyChain i x x≰bot nt = record
        { lo         = atom i
        ; hi         = can x nt
        ; lo-proper  = can-proper (bot {i}) (nondeg i)
        ; hi-proper  = can-proper x nt
        ; lo≤hi      = ≤ᵖ-sound {atom i} {can x nt} (atom-≤ x nt)
        ; hi≰lo      = strict
        }
        where
        -- Retract a comparison can x ≤ atom i onto the canopy: x ≤ bot.
        strict : ¬ (≤ᴸ._≤_ (can x nt) (atom i))
        strict le = x≰bot
          (≤trans (≤reflexive (≈sym (≈trans (π-cong i (≈ᵖ-sym (↑-can x nt))) (π∘↑ x))))
                  (≤trans (π-mono i (≤ᵖ-complete {can x nt} {atom i} le))
                          (≤reflexive (π-atom {i}))))

    -- (D2): canopy p carries the chain of color true, canopy q of color false.
    chains : (c : Bool) → Σ[ k ∈ ProperChain ] color (ProperChain.lo k) ≡ c
    chains true   = canopyChain p xₚ xₚ≰bot xₚ-nonTop  , dec-true (p ≟ p) refl
    chains false  = canopyChain q x_q x_q≰bot x_q-nonTop , dec-false (q ≟ p) (λ q≡p → p≢q (sym q≡p))

    -- The parachute is a D-lattice ...
    parachute-DPartition : DPartition
    parachute-DPartition = record { color = color ; same-color = same-color ; chain = chains }

    -- ... and hence, by Aschbacher's (1.2), an A-lattice.
    parachute-ALattice : IsALattice
    parachute-ALattice = D→A parachute-DPartition
```

---

[^1]: M. Aschbacher, *On intervals in subgroup lattices of finite groups*,
      J. Amer. Math. Soc. 21 (2008), 809–830: the definitions of A-, D-, `C*`-,
      `C∗`-, and CD-lattices are in its introduction, and (1.2) is the lemma
      "B-lattices and D-lattices are A-lattices" of its Section 1.  The
      specialization to parachutes, and its consequences for the enforcement
      catalog, are recorded in `docs/notes/flrp-rp2-catalog.md`.
