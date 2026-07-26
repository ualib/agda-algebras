---
layout: default
file: "src/FLRP/Parachute.lagda.md"
title: "FLRP.Parachute module (The Agda Universal Algebra Library)"
date: "2026-07-25"
author: "the agda-algebras development team"
---

### Parachute representations and core-freeness

This is the [FLRP.Parachute][] module of the [Agda Universal Algebra Library][].

A **parachute representation** is a group `G` with a subgroup `H` whose upper
interval `[H , G]` has the shape of a parachute: a bottom `H` covered by `n` atoms
`K₁ , … , Kₙ`, distinct atoms meeting at `H` and joining to `G`, and every member of
the interval other than `H` lying above one of the atoms.  This module states that
shape as group-theoretic data (`ParachuteConfig`{.AgdaRecord}) and proves the
theorem the note's § 3.3 turns on:[^1]

> if `H` is core-free and at least two canopies have more than two elements, then
> **every proper member of `[H , G]` is core-free**.

That is the engine of the note's Theorem 3.6, of Lemma 3.7, and of Corollary 3.8:
core-freeness propagates from the bottom of a parachute to every proper subgroup
above it, so a cf-IE property enforced by a canopy `Lᵢ` applies to `G` through the
representation `[Kᵢ , G] ≅ Lᵢ`.

The argument is exactly the note's.  Let `Y` be proper, let `N = Core_G(Y)`, and
consider `NH`.  It lies in `Y`, hence is proper.  If it collapses to `H` then `N`
is a normal subgroup inside `H`, so `N = 1` by core-freeness and we are done.
Otherwise `NH` lies above some atom `Kₘ`; pick one of the two big canopies, say the
`r`-th with `r ≠ m`, and observe that its atom `Kᵣ` and its middle element `Z` are
*both* complements of `NH` in `[H , G]` that permute with it — the permutation
because `N` is normal.  Corollary 3.5 ([Classical.Structures.Group.Complements][])
then forces `Kᵣ` and `Z` to be incomparable, contradicting `Kᵣ < Z`.

**Constructive shape.**  The note argues by contradiction from "`N ≠ 1`"; here the
same steps read as a direct proof, because the parachute's covering property is
*data*: `covered`{.AgdaField} decides, for each member of the interval, whether it
collapses to `H` or lies above an atom.  In the first case core-freeness of `H`
finishes; only the second case needs a contradiction, and there one is genuinely
available.  Nothing is weakened and no double negation is introduced.

The note's Lemma 3.7 (i) — "`NY = G` for every `H ≤ Y < G`" — appears below in its
constructive contrapositive: a normal subgroup contained in a *proper* member of the
interval is trivial (`normal-in-proper-trivial`{.AgdaFunction}).  Over a finite
group the two readings are classically equivalent, and this one carries the same
information without deciding whether `N` is trivial.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.Parachute where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using  ( ⊥ ; ⊥-elim )
open import Data.Fin.Base                          using  ( Fin )
open import Data.Fin.Properties                    using  ( _≟_ )
open import Data.Nat.Base                          using  ( ℕ )
open import Data.Product                           using  ( _,_ ; _×_ ; Σ-syntax
                                                          ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using  ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Unit.Base                         using  ( tt )
open import Level                                  using  ( Level ; 0ℓ ; lift )
                                                   renaming ( suc to lsuc )
open import Relation.Binary.PropositionalEquality  using  ( _≡_ ; refl ; sym ; trans )
open import Relation.Nullary                       using  ( ¬_ ; yes ; no )
open import Relation.Unary                         using  ( Pred ; _∈_ ; _⊆_ ; _∩_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Group  using  ( Group ; IsSubgroup ; module Core
                                               ; module Complements ; module Complex
                                               ; module Conj ; module Group-Op
                                               ; module GroupSublattice
                                               ; fullSubgroup ; trivialSubgroup )
open import FLRP.Enforceable            using  ( module UpperInterval ; CoreFree )
open import Setoid.Algebras             using  ( 𝕌[_] )
```
-->

#### The interval, with meets and the two ends

Throughout, `𝒢`{.AgdaBound} is a group and `H`{.AgdaBound} a subgroup; the interval
`[H , G]` is the `UpperInterval`{.AgdaModule} of [FLRP.Enforceable][].

```agda
module GroupParachute
  (𝒢     : Group 0ℓ 0ℓ)
  (H     : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ)
  (H-sg  : IsSubgroup 𝒢 H)
  where

  open UpperInterval 𝒢 H H-sg
  open Complements 𝒢       using  ( mem-∙ᶜˡ ; mem-∙ᶜʳ ; Factorize
                                  ; Factorize-sym ; normal-∙ᶜ-isSubgroup
                                  ; complement-⊆-collapse )
  open Complex 𝒢           using  ( _∙ᶜ_ ; ∙ᶜ-mono ; subgroup-∙ᶜ-idem )
  open Conj 𝒢              using  ( IsNormal )
  open Group-Op 𝒢          using  ( ε )
  open GroupSublattice 𝒢 0ℓ  using  ( ∧-isSubgroup )
  open IsSubgroup          using  ( ε-closed )
```

`IsAll M` says the interval element `M` is all of `G` — the top of the interval.
Its negation is the note's `M < G`.

```agda
  -- M exhausts the group.
  IsAll : Interval≈ → Type 0ℓ
  IsAll M = ∀ x → x ∈ set M

  -- M is a proper member of the interval.
  Proper : Interval≈ → Type 0ℓ
  Proper M = ¬ (IsAll M)
```

The two ends of the interval, as members of it: the bottom is `H` itself and the top
is the full subgroup.  `IsAll`{.AgdaFunction} is containment of the top, spelled
pointwise.

```agda
  -- The bottom and the top of [H , G].
  Hᵢ : Interval≈
  Hᵢ = mk H H-sg (λ z → z)

  Gᵢ : Interval≈
  Gᵢ = mk  (proj₁ (fullSubgroup 𝒢 0ℓ)) (proj₂ (fullSubgroup 𝒢 0ℓ)) (λ _ → lift tt)

  IsAll→⊇ : (M : Interval≈) → IsAll M → set Gᵢ ⊆ set M
  IsAll→⊇ M all {x} _ = all x

  ⊇→IsAll : (M : Interval≈) → set Gᵢ ⊆ set M → IsAll M
  ⊇→IsAll M sub x = sub {x} (lift tt)

  -- Interval equality is mutual containment, so it composes pointwise.
  ≈ᵢ-trans : {M N R : Interval≈} → M ≈ᵢ N → N ≈ᵢ R → M ≈ᵢ R
  ≈ᵢ-trans (M⊆N , N⊆M) (N⊆R , R⊆N) = (λ z → N⊆R (M⊆N z)) , (λ z → N⊆M (R⊆N z))
```

The meet of two interval elements is their intersection: a subgroup because meets in
the subgroup lattice are intersections, and above `H` because both factors are.

```agda
  infixr 7 _∧ᵢ_

  _∧ᵢ_ : Interval≈ → Interval≈ → Interval≈
  M ∧ᵢ N = mk  (set M ∩ set N)
               (∧-isSubgroup (sublat M) (sublat N)
                             (element-isSubgroup M) (element-isSubgroup N))
               (λ h → above M h , above N h)
```

#### The parachute shape, as group-theoretic data

`ParachuteConfig n` is the shape of `[H , G]` that the argument consumes: `n` atoms,
distinct ones meeting at the bottom and joining to the top, and the covering
property.  The fields are exactly the hypotheses the theorem below uses — nothing
about the canopies themselves is needed, which is why the theorem applies verbatim
however the canopies are presented.

```agda
  record ParachuteConfig (n : ℕ) : Type (lsuc 0ℓ) where
    field
      -- The n atoms of the interval.
      atom        : Fin n → Interval≈

      -- Distinct atoms meet at the bottom ...
      atoms-meet  : (i j : Fin n) → ¬ (i ≡ j) → (set (atom i) ∩ set (atom j)) ⊆ H

      -- ... and join to the top: nothing proper contains two distinct atoms.
      atoms-join  : (i j : Fin n) → ¬ (i ≡ j) → (C : Interval≈)
                  → set (atom i) ⊆ set C → set (atom j) ⊆ set C → IsAll C

      -- The bottom is covered by the atoms: every member of the interval either
      -- collapses to H or lies above an atom.
      covered     : (M : Interval≈)
                  → (set M ⊆ H) ⊎ (Σ[ i ∈ Fin n ] (set (atom i) ⊆ set M))
```

A canopy has **more than two elements** when its atom is strictly below some proper
member of the interval — the note's `|Lᵢ| > 2`.

```agda
  record BigCanopy (K : Interval≈) : Type (lsuc 0ℓ) where
    field
      -- An element strictly between the atom K and the top.
      mid         : Interval≈
      atom-⊆-mid  : set K ⊆ set mid
      mid-⊄-atom  : ¬ (set mid ⊆ set K)
      mid-proper  : Proper mid
```

#### The subgroup `N H`

For an interval element `Y`, write `N` for the core of `Y` in `G` and `NH` for the
complex product `N H`.  It is a subgroup because `N` is normal
(`normal-∙ᶜ-isSubgroup`{.AgdaFunction}), it contains `H` and `N`, and it is
contained in `Y`, since `Y` contains both factors and absorbs its own square.

```agda
  module CoreProduct (Y : Interval≈) where

    Y-sg : IsSubgroup 𝒢 (set Y)
    Y-sg = element-isSubgroup Y

    private module CY = Core 𝒢 (set Y) Y-sg

    -- The core of Y in G: a normal subgroup of G contained in Y.
    N : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ
    N = proj₁ CY.core

    N-sg : IsSubgroup 𝒢 N
    N-sg = CY.core-isSubgroup

    N-normal : IsNormal N
    N-normal = CY.core-normal

    -- The subgroup N H, as a member of the interval.
    NH : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ
    NH = N ∙ᶜ H

    NH-sg : IsSubgroup 𝒢 NH
    NH-sg = normal-∙ᶜ-isSubgroup N-normal N-sg H-sg

    H⊆NH : H ⊆ NH
    H⊆NH = mem-∙ᶜʳ (ε-closed N-sg)

    N⊆NH : N ⊆ NH
    N⊆NH = mem-∙ᶜˡ (ε-closed H-sg)

    NHᵢ : Interval≈
    NHᵢ = mk NH NH-sg H⊆NH

    -- N H lies inside Y, so it is proper whenever Y is.
    NH⊆Y : NH ⊆ set Y
    NH⊆Y z = proj₁ (subgroup-∙ᶜ-idem Y-sg) (∙ᶜ-mono CY.core-⊆ (above Y) z)

    NH-proper : Proper Y → Proper NHᵢ
    NH-proper Y-proper all = Y-proper (λ x → NH⊆Y (all x))
```

#### Core-freeness propagates to every proper member of a parachute

The theorem: in a parachute representation over a core-free `H`, with two canopies
of more than two elements, every proper member of `[H , G]` is core-free.

```agda
  module _ {n : ℕ} (𝑃 : ParachuteConfig n) where
    open ParachuteConfig 𝑃

    proper-CoreFree :
         CoreFree 𝒢 H H-sg
      →  {p q : Fin n} → ¬ (p ≡ q)
      →  BigCanopy (atom p) → BigCanopy (atom q)
      →  (Y : Interval≈) → Proper Y
      →  CoreFree 𝒢 (set Y) (element-isSubgroup Y)
    proper-CoreFree cf {p} {q} p≢q big-p big-q Y Y-proper = branch (covered NHᵢ)
      where
      open CoreProduct Y

      -- If N H collapses to H then N is a normal subgroup inside H, hence trivial.
      collapse : NH ⊆ H → CoreFree 𝒢 (set Y) Y-sg
      collapse NH⊆H z = cf (Core.core-greatest 𝒢 H H-sg N-normal (λ w → NH⊆H (N⊆NH w)) z)

      -- Otherwise N H lies above an atom Kₘ, and we derive a contradiction.
      module Above (m : Fin n) (Kₘ⊆NH : set (atom m) ⊆ NH) where

        -- One of the two big canopies has an index other than m.
        other : Σ[ r ∈ Fin n ] (¬ (r ≡ m) × BigCanopy (atom r))
        other with p ≟ m
        ... | no  p≢m  = p , p≢m , big-p
        ... | yes p≡m  = q , (λ q≡m → p≢q (trans p≡m (sym q≡m))) , big-q

        private
          r     = proj₁ other
          r≢m   = proj₁ (proj₂ other)
          big-r = proj₂ (proj₂ other)

        open BigCanopy big-r using ( mid ; atom-⊆-mid ; mid-⊄-atom ; mid-proper )

        -- Any proper W above the r-th atom meets N H in H: an atom below the
        -- meet would have to be the m-th (else it joins with Kₘ inside N H,
        -- making N H everything), and then Kₘ and Kᵣ both sit inside W.
        meet-⊆H : (W : Interval≈) → set (atom r) ⊆ set W → Proper W → (NH ∩ set W) ⊆ H
        meet-⊆H W Kᵣ⊆W W-proper {x} x∈ with covered (NHᵢ ∧ᵢ W)
        ... | inj₁ meet⊆H       = meet⊆H x∈
        ... | inj₂ (s , Kₛ⊆)    with s ≟ m
        ...   | no  s≢m  = ⊥-elim (NH-proper Y-proper
                             (atoms-join s m s≢m NHᵢ (λ z → proj₁ (Kₛ⊆ z)) Kₘ⊆NH))
        ...   | yes refl = ⊥-elim (W-proper
                             (atoms-join r m r≢m W Kᵣ⊆W (λ z → proj₂ (Kₛ⊆ z))))

        -- Any W above the r-th atom factorizes the group with N H: the subgroup
        -- N W contains both Kᵣ and Kₘ, hence is everything, and it sits inside
        -- (N H) W.
        factorize : (W : Interval≈) → set (atom r) ⊆ set W → Factorize (set W) NH
        factorize W Kᵣ⊆W = Factorize-sym NH-sg W-sg product-is-all
          where
          W-sg : IsSubgroup 𝒢 (set W)
          W-sg = element-isSubgroup W

          NWᵢ : Interval≈
          NWᵢ = mk  (N ∙ᶜ set W)
                    (normal-∙ᶜ-isSubgroup N-normal N-sg W-sg)
                    (λ h → mem-∙ᶜʳ (ε-closed N-sg) (above W h))

          all-NW : IsAll NWᵢ
          all-NW = atoms-join r m r≢m NWᵢ
                     (λ z → mem-∙ᶜʳ (ε-closed N-sg) (Kᵣ⊆W z))
                     (λ z → ∙ᶜ-mono (λ w → w) (above W) (Kₘ⊆NH z))

          product-is-all : Factorize NH (set W)
          product-is-all x = ∙ᶜ-mono N⊆NH (λ w → w) (all-NW x)

        -- Corollary 3.5 applied to the two comparable complements Kᵣ ≤ Z of N H.
        contradiction : ⊥
        contradiction = mid-⊄-atom
          (complement-⊆-collapse
             (element-isSubgroup (atom r)) (element-isSubgroup mid)
             (above (atom r)) atom-⊆-mid
             (meet-⊆H mid (λ z → atom-⊆-mid z) mid-proper)
             (factorize (atom r) (λ z → z)))

      branch : (NH ⊆ H) ⊎ (Σ[ i ∈ Fin n ] (set (atom i) ⊆ NH))
             → CoreFree 𝒢 (set Y) Y-sg
      branch (inj₁ NH⊆H)          = collapse NH⊆H
      branch (inj₂ (m , Kₘ⊆NH))   = λ _ → ⊥-elim (Above.contradiction m Kₘ⊆NH)
```

#### Lemma 3.7 (i)

A normal subgroup of `G` contained in a proper member of the interval is trivial:
this is the note's "`NY = G` for all `H ≤ Y < G`", read contrapositively.  Applied
to `Y = NH` it says `NH = G` for every nontrivial normal `N`, which is the form the
note uses.

```agda
    normal-in-proper-trivial :
         CoreFree 𝒢 H H-sg
      →  {p q : Fin n} → ¬ (p ≡ q)
      →  BigCanopy (atom p) → BigCanopy (atom q)
      →  (Y : Interval≈) → Proper Y
      →  {ℓⁿ : Level} {N : Pred 𝕌[ proj₁ 𝒢 ] ℓⁿ}
      →  IsNormal N → N ⊆ set Y
      →  N ⊆ proj₁ (trivialSubgroup 𝒢)
    normal-in-proper-trivial cf p≢q big-p big-q Y Y-proper N-normal N⊆Y z =
      proper-CoreFree cf p≢q big-p big-q Y Y-proper
        (Core.core-greatest 𝒢 (set Y) (element-isSubgroup Y) N-normal N⊆Y z)

    -- The note's "N H = G": if the product N H is proper, then N is trivial.
    normal-∙ᶜH-all :
         CoreFree 𝒢 H H-sg
      →  {p q : Fin n} → ¬ (p ≡ q)
      →  BigCanopy (atom p) → BigCanopy (atom q)
      →  (Y : Interval≈) → Proper (CoreProduct.NHᵢ Y)
      →  CoreProduct.N Y ⊆ proj₁ (trivialSubgroup 𝒢)
    normal-∙ᶜH-all cf p≢q big-p big-q Y NH-proper =
      normal-in-proper-trivial cf p≢q big-p big-q (CoreProduct.NHᵢ Y) NH-proper
        (CoreProduct.N-normal Y) (CoreProduct.N⊆NH Y)
```

---

[^1]: `docs/papers/flrp/ieprops/IEProps-1205.1927v4.tex`, Theorem 3.6
      (`thm-wjd-1`) and Lemma 3.7 (`lemma-wjd-5`); see also
      [`docs/notes/flrp-research-roadmap.md`](docs/notes/flrp-research-roadmap.md) § 4
      and the design note `docs/notes/flrp-rp1-parachutes.md`.
