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
open import Relation.Nullary                       using  ( ¬_ ; Dec ; yes ; no )
open import Relation.Unary                         using  ( Pred ; _∈_ ; _⊆_ ; _∩_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Group  using  ( Group ; IsSubgroup ; module Core
                                               ; module Centralizer ; module Complements
                                               ; module Complex ; module Conj
                                               ; module Group-Op ; module GroupSublattice
                                               ; dedekindʳ
                                               ; fullSubgroup ; trivialSubgroup )
open import Relation.Binary             using  ( Setoid )
open import Setoid.Algebras             using  ( 𝔻[_] )
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
  open Centralizer 𝒢       using  ( C[_] ; C-isAntitone ; C-isSubgroup ; C-isNormal
                                  ; normals-centralize )
  open Conj 𝒢              using  ( conj ; IsNormal ; conj-congᵍ ; conj-action-∙ )
  open Group-Op 𝒢          using  ( _∙_ ; ε ; _⁻¹ ; ∙-cong ; idˡ-law )
  open Setoid 𝔻[ proj₁ 𝒢 ] using  ( _≈_ ) renaming ( refl to ≈refl ; sym to ≈sym
                                                   ; trans to ≈trans )
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

`ParachuteConfig n` states the shape of `[H , G]`: `n` atoms, distinct ones meeting
at the bottom and joining to the top, and the covering property.  Nothing about the
canopies themselves appears, which is why the results below apply verbatim however
the canopies are presented.  (`proper-CoreFree`{.AgdaFunction} consumes only
`atoms-join`{.AgdaField} and `covered`{.AgdaField}; `atoms-meet`{.AgdaField} records
the other half of the picture — it is what keeps the atoms distinct — and is used by
the consumers that establish properness of an atom.)

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

#### Lemma 3.7: the structure of a core-free parachute representation

The note's Lemma 3.7 describes the normal structure that a parachute forces: for
every nontrivial normal `N` one has `NH = G` and `C_G(N) = 1`, and consequently `G`
is subdirectly irreducible with a nonabelian monolith.  The module below proves this
under two further hypotheses, both of them consequences of *finiteness* that the
library cannot yet derive and that are therefore threaded as ordinary arguments.

+  **Decidable properness** `all?`{.AgdaBound}.  The note's argument moves freely
   between "`NH` is proper" and "`NH = G`"; constructively `IsAll`{.AgdaFunction} is
   a Π-statement, so the step from `¬ ¬ IsAll` to `IsAll` needs a decision.  Over a
   parachute the decision is *free* — the image of a member of the interval is the
   top, the bottom, or a canopy element, and only the first is everything — and
   [FLRP.Parachute.Representation][] supplies it.  This is the ADR-008 layer
   discipline: the obstruction is real, so the decision procedure becomes data.

+  **A minimal normal subgroup** `M`{.AgdaBound}.  The centralizer argument descends
   to a minimal nontrivial normal subgroup; existence follows from finiteness by
   well-founded descent, which the library does not yet have.

+  **A strictly intermediate member** `K`{.AgdaBound}, that is, `H < K < G`.  In a
   parachute with `n ≥ 2` any atom will do, and the theorems module passes one.

```agda
    module Structure
      (H-cf     : CoreFree 𝒢 H H-sg)
      {p q      : Fin n} (p≢q : ¬ (p ≡ q))
      (big-p    : BigCanopy (atom p)) (big-q : BigCanopy (atom q))
      (all?     : (M : Interval≈) → Dec (IsAll M))
      (K        : Interval≈) (K-proper : Proper K) (K-⊄H : ¬ (set K ⊆ H))
      where

      private
        Triv : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ
        Triv = proj₁ (trivialSubgroup 𝒢)

        K-sg : IsSubgroup 𝒢 (set K)
        K-sg = element-isSubgroup K

      -- The propagation theorem, in the form Lemma 3.7 uses.
      normal-in-proper : (Y : Interval≈) → Proper Y
        → {N : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ} → IsNormal N → N ⊆ set Y → N ⊆ Triv
      normal-in-proper Y Y-proper = normal-in-proper-trivial H-cf p≢q big-p big-q Y Y-proper

      -- The member N H of the interval, for an arbitrary normal subgroup N.
      NHof : (N : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ) → IsSubgroup 𝒢 N → IsNormal N → Interval≈
      NHof N N-sg N-nrm =
        mk (N ∙ᶜ H) (normal-∙ᶜ-isSubgroup N-nrm N-sg H-sg) (mem-∙ᶜʳ (ε-closed N-sg))
```

**Lemma 3.7 (i), first half**: `NH = G` for every nontrivial normal `N`.  Were `NH`
proper, `N` would sit inside a proper member of the interval and hence be trivial;
the decision procedure turns that into the positive statement.

```agda
      NH-all : (N : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ) (N-sg : IsSubgroup 𝒢 N) (N-nrm : IsNormal N)
        → ¬ (N ⊆ Triv) → IsAll (NHof N N-sg N-nrm)
      NH-all N N-sg N-nrm nontriv with all? (NHof N N-sg N-nrm)
      ... | yes a  = a
      ... | no ¬a  = ⊥-elim (nontriv (normal-in-proper (NHof N N-sg N-nrm) ¬a N-nrm
                                                       (mem-∙ᶜˡ (ε-closed H-sg))))
```

**Lemma 3.7 (i), second half**: the centralizer of a *minimal* nontrivial normal
subgroup `M` is trivial.  Suppose not; then `C = C_G(M)` is a nontrivial normal
subgroup, so `CH = G`.  Now `M ∩ K` is normalized by `C H`, hence by all of `G`: an
element of `H` normalizes it because it normalizes both `M` and `K`, and an element
of `C` fixes every member of `M` pointwise.  And `M ∩ K` is nontrivial, by Dedekind's
rule: `K = K ∩ MH = (M ∩ K)H`, which would collapse `K` into `H`.  Minimality of `M`
then puts `M` inside `K`, so `MH ⊆ K` is proper — contradicting `MH = G`.

```agda
      module Minimal
        (M          : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ)
        (M-sg       : IsSubgroup 𝒢 M)
        (M-nrm      : IsNormal M)
        (M-nontriv  : ¬ (M ⊆ Triv))
        (M-min      : {N : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ} → IsSubgroup 𝒢 N → IsNormal N
                    → N ⊆ M → ¬ (N ⊆ Triv) → M ⊆ N)
        where

        private
          C-sg : IsSubgroup 𝒢 C[ M ]
          C-sg = C-isSubgroup M

          C-nrm : IsNormal C[ M ]
          C-nrm = C-isNormal M-nrm

          -- M ∩ K is a subgroup (a meet in the subgroup lattice).
          MK-sg : IsSubgroup 𝒢 (M ∩ set K)
          MK-sg = ∧-isSubgroup (M , IsSubgroup.isSubuniverse M-sg) (sublat K) M-sg K-sg

          M-all : IsAll (NHof M M-sg M-nrm)
          M-all = NH-all M M-sg M-nrm M-nontriv

        -- M ∩ K is nontrivial: otherwise Dedekind's rule collapses K into H.
        MK-nontriv : ¬ ((M ∩ set K) ⊆ Triv)
        MK-nontriv MK⊆triv = K-⊄H inside
          where
          inside : set K ⊆ H
          inside {x} x∈K = IsSubgroup.respects H-sg (≈sym x≈h) h∈H
            where
            split : x ∈ (M ∩ set K) ∙ᶜ H
            split = proj₂ (dedekindʳ 𝒢 {H = H} {C = M} {K = set K} K-sg (above K))
                          (M-all x , x∈K)

            h    = proj₁ (proj₂ split)
            h∈H  = proj₁ (proj₂ (proj₂ (proj₂ split)))

            x≈h : x ≈ h
            x≈h = ≈trans (proj₂ (proj₂ (proj₂ (proj₂ split))))
                         (≈trans (∙-cong (MK⊆triv (proj₁ (proj₂ (proj₂ split)))) ≈refl)
                                 (idˡ-law h))

        -- Were the centralizer nontrivial, M ∩ K would be normal in G.
        private
          MK-normal : IsAll (NHof C[ M ] C-sg C-nrm) → IsNormal (M ∩ set K)
          MK-normal all g {x} (x∈M , x∈K) = M-nrm g x∈M , K-mem
            where
            factor = all g
            c      = proj₁ factor
            h      = proj₁ (proj₂ factor)
            c∈C    = proj₁ (proj₂ (proj₂ factor))
            h∈H    = proj₁ (proj₂ (proj₂ (proj₂ factor)))
            g≈ch   = proj₂ (proj₂ (proj₂ (proj₂ factor)))

            -- Conjugating by an element of H stays inside both M and K.
            hx∈K : conj h x ∈ set K
            hx∈K = IsSubgroup.∙-closed K-sg
                     (IsSubgroup.∙-closed K-sg (above K h∈H) x∈K)
                     (IsSubgroup.⁻¹-closed K-sg (above K h∈H))

            hx∈M : conj h x ∈ M
            hx∈M = M-nrm h x∈M

            -- Conjugating a member of M by an element of its centralizer fixes it.
            fixed : conj c (conj h x) ≈ conj h x
            fixed = ≈trans (∙-cong (c∈C (conj h x) hx∈M) ≈refl)
                           (≈trans (Group-Op.assoc-law 𝒢 (conj h x) c (c ⁻¹))
                                   (≈trans (∙-cong ≈refl (Group-Op.invʳ-law 𝒢 c))
                                           (Group-Op.idʳ-law 𝒢 (conj h x))))

            K-mem : conj g x ∈ set K
            K-mem = set-respects K
                      (≈sym (≈trans (conj-congᵍ x g≈ch)
                                    (≈trans (conj-action-∙ c h x) fixed)))
                      hx∈K

        -- Lemma 3.7 (i), second half.
        centralizer-trivial : C[ M ] ⊆ Triv
        centralizer-trivial =
          normal-in-proper (NHof C[ M ] C-sg C-nrm) C-proper C-nrm (mem-∙ᶜˡ (ε-closed H-sg))
          where
          C-proper : Proper (NHof C[ M ] C-sg C-nrm)
          C-proper all = K-proper (λ x → M⊆K (M-all x))
            where
            M⊆M∩K : M ⊆ (M ∩ set K)
            M⊆M∩K = M-min MK-sg (MK-normal all) (λ z → proj₁ z) MK-nontriv

            -- M inside K forces M H inside K, and M H is everything.
            M⊆K : (M ∙ᶜ H) ⊆ set K
            M⊆K z = proj₁ (subgroup-∙ᶜ-idem K-sg)
                      (∙ᶜ-mono (λ w → proj₂ (M⊆M∩K w)) (above K) z)

        -- The note's Remark: a nontrivial normal subgroup is nonabelian, since an
        -- abelian one lies inside its own (trivial) centralizer.
        nonabelian : ¬ (∀ x y → x ∈ M → y ∈ M → x ∙ y ≈ y ∙ x)
        nonabelian abelian =
          M-nontriv (λ {x} x∈M → centralizer-trivial (λ y y∈M → abelian x y x∈M y∈M))

        -- Lemma 3.7 (ii), pairwise form: no nontrivial normal subgroup meets M
        -- trivially, so M is the monolith and G is subdirectly irreducible.
        normals-meet : (N : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ) → IsSubgroup 𝒢 N → IsNormal N
          → (∀ {w} → w ∈ M → w ∈ N → w ≈ ε) → N ⊆ Triv
        normals-meet N N-sg N-nrm meet z =
          centralizer-trivial (normals-centralize M-sg N-sg M-nrm N-nrm meet z)

      -- The centralizer of *any* nontrivial normal subgroup with a minimal normal
      -- subgroup inside it is trivial, since centralizers are antitone.
      centralizer-of-normal :
           (M N : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ)
        →  (M-sg : IsSubgroup 𝒢 M) (M-nrm : IsNormal M) (M-nontriv : ¬ (M ⊆ Triv))
        →  ({R : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ} → IsSubgroup 𝒢 R → IsNormal R
              → R ⊆ M → ¬ (R ⊆ Triv) → M ⊆ R)
        →  M ⊆ N → C[ N ] ⊆ Triv
      centralizer-of-normal M N M-sg M-nrm M-nontriv M-min M⊆N z =
        Minimal.centralizer-trivial M M-sg M-nrm M-nontriv M-min (C-isAntitone M⊆N z)
```

---

[^1]: `docs/papers/flrp/ieprops/IEProps-1205.1927v4.tex`, Theorem 3.6
      (`thm-wjd-1`) and Lemma 3.7 (`lemma-wjd-5`); see also
      [`docs/notes/flrp-research-roadmap.md`](docs/notes/flrp-research-roadmap.md) § 4
      and the design note `docs/notes/flrp-rp1-parachutes.md`.
