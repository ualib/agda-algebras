---
layout: default
file: "src/FLRP/KurzweilInterval.lagda.md"
title: "FLRP.KurzweilInterval module (The Agda Universal Algebra Library)"
date: "2026-07-27"
author: "the agda-algebras development team"
---

### Kurzweil's interval `[D , Sⁿ] ≅ Eq(n)′`

This is the [FLRP.KurzweilInterval][] module of the [Agda Universal Algebra Library][].

This module packages the group infrastructure of issue #521 — the power
`Sⁿ`{.AgdaFunction}, its diagonal `D`{.AgdaFunction}, and the partition subgroups
`K_π` — into the interval presentation the FLRP program consumes: the upper
interval `[D , Sⁿ]` as an `UpperInterval`{.AgdaModule} instance of
[FLRP.Enforceable][], and **Kurzweil's lemma** — the interval is isomorphic to the
*dual* of the partition lattice `Eq(n)` of
[Classical.Structures.Lattice.Partitions][] — as an
`IntervalIso`{.AgdaFunction}.

The classical statement (Kurzweil 1985; `lem:latt-duals` of
`docs/papers/fin-lat-rep/SmallLatticeReps.tex`, discussed in DeMeo's thesis
§ 2.2) splits into two halves of very different characters, and the formal
treatment mirrors the split honestly:

+  **The dual order embedding is proved outright.**  `π ↦ K_π` lands in the
   interval, reverses the refinement order in both directions, and is injective
   up to kernel equality — this is the content the written sources actually
   prove, it is finite combinatorics, and it needs only a *nontrivial* base
   group ([Classical.Structures.Group.PartitionSubgroup][]).

+  **Surjectivity is a registered hypothesis.**  That *every* respecting subgroup
   between `D` and `Sⁿ` is a partition subgroup is the half where `S` must be a
   finite *nonabelian simple* group; the sources cite it to Kurzweil's article
   without reproof, and its formalization needs the normal-subgroup structure
   theory of powers of a simple group (subdirect products, block inductions) that
   the library does not yet have — real group theory, not bookkeeping.  Per the
   `--safe` discipline it enters as the explicit hypothesis
   `KurzweilSurjectivity`{.AgdaFunction}, registered as **Entry 4** of
   [FLRP.Assumptions][]; it is stated in the Σ-form that *hands the consumer the
   partition witness*, which is exactly what the isomorphism's inverse map needs.
   Retiring the entry — proving surjectivity for a nonabelian simple base — is
   the follow-up flagged in issue #521, and upgrades
   `kurzweilIntervalIso`{.AgdaFunction} with no change to consumers.

Given the hypothesis, `kurzweilIntervalIso`{.AgdaFunction} *is a theorem*:
`[D , Sⁿ] ≅ (Eq n)′` in the `IntervalIso` presentation, with the dual order
handled by `≤ᵈ-flip`{.AgdaFunction} / `≤ᵈ-unflip`{.AgdaFunction} of
[Classical.Structures.Lattice.Dual][] and the refinement order bridged to the
lattice meet order by `⊑→≤`{.AgdaFunction} / `≤→⊑`{.AgdaFunction}.  The
corollary `eqDual-groupRepresentable`{.AgdaFunction} — the dual partition
lattice is group representable — is the form RP-4's wreath no-go (issue #461)
consumes, and the consumer-interface module at the bottom records the composite
signature the Kurzweil–Netter duality proof (issue #502) will call.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.KurzweilInterval where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Nat.Base   using ( ℕ )
open import Data.Product    using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Level           using ( 0ℓ ) renaming ( suc to lsuc )
open import Relation.Binary using ( Setoid )
open import Relation.Nullary  using ( ¬_ )
open import Relation.Unary    using ( _⊆_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Group.Basic             using  ( Group
                                                                ; module Group-Op )
open import Classical.Structures.Group.GSet              using  ( module CosetAction )
open import Classical.Structures.Group.PartitionSubgroup using  ( module PartitionSubgroups )
open import Classical.Structures.Lattice.Dual            using  ( module LatticeDual
                                                                ; dualLattice )
open import Classical.Structures.Lattice.Partitions      using  ( EqLattice ; _⊑_
                                                                ; _≈ᵖ_ ; ⊑→≤ ; ≤→⊑ )
open import FLRP.Enforceable    using  ( module UpperInterval ; IntervalIso
                                       ; GroupRepresentable )
open import FLRP.Problem        using  ( ConIso )
open import Order.Iso           using  ( OrderIso )
open import Setoid.Algebras     using  ( 𝕌[_] ; 𝔻[_] )
open import Setoid.Congruences.Certificates.Schema  using  ( ParentVec )
```
-->

#### The interval `[D , Sⁿ]` and the surjectivity hypothesis

`KurzweilInterval`{.AgdaModule} `𝒮` `n` fixes the base group and the exponent,
instantiates the partition-subgroup toolkit, and opens the upper interval at the
diagonal.

```agda
module KurzweilInterval (𝒮 : Group 0ℓ 0ℓ) (n : ℕ) where

  open PartitionSubgroups n 𝒮 public

  -- The power Sⁿ (the ⨅ᵍ-Group of the opened toolkit, named for readability).
  Sⁿ : Group 0ℓ 0ℓ
  Sⁿ = ⨅ᵍ-Group

  open UpperInterval Sⁿ Diag Diag-isSubgroup public

  -- A partition subgroup, as an element of the interval [D , Sⁿ].
  toInterval : ParentVec n → Interval≈
  toInterval pv = mk (K pv) (K-isSubgroup pv) (Diag⊆K pv)
```

**Entry 4 of the assumptions registry** ([FLRP.Assumptions][]): every interval
element is extensionally a partition subgroup, *with the partition produced as
data*.  The classical theorem asserts this whenever `𝒮` is a finite nonabelian
simple group; the registry documents source, status, and retirement path.

```agda
  -- Kurzweil surjectivity: every respecting subgroup in [D , Sⁿ] is K_π for
  -- a produced partition π.
  KurzweilSurjectivity : Type (lsuc 0ℓ)
  KurzweilSurjectivity =
    (𝑴 : Interval≈) → Σ[ pv ∈ ParentVec n ] ((set 𝑴 ⊆ K pv) × (K pv ⊆ set 𝑴))
```

#### The interval isomorphism `[D , Sⁿ] ≅ Eq(n)′`

Under the surjectivity hypothesis and a nontriviality witness for the base
group, `π ↦ K_π` and the produced partitions are a mutually inverse monotone
pair between the interval and the *dual* of `Eq(n)`: order reversal turns the
interval order into the dual lattice order, with the round trips repaired by
order reflection (`K-reflects`{.AgdaFunction}) and injectivity
(`K-injective`{.AgdaFunction}).

```agda
  module _ (s : 𝕌[ proj₁ 𝒮 ]) (s≉ε : ¬ (Setoid._≈_ 𝔻[ proj₁ 𝒮 ] s (Group-Op.ε 𝒮)))
           (surj : KurzweilSurjectivity)
    where

    open LatticeDual (EqLattice n) using ( ≤ᵈ-flip ; ≤ᵈ-unflip )

    private
      -- The partition attached to an interval element by the hypothesis.
      part : Interval≈ → ParentVec n
      part 𝑴 = proj₁ (surj 𝑴)

      part-in : (𝑴 : Interval≈) → set 𝑴 ⊆ K (part 𝑴)
      part-in 𝑴 = proj₁ (proj₂ (surj 𝑴))

      part-out : (𝑴 : Interval≈) → K (part 𝑴) ⊆ set 𝑴
      part-out 𝑴 = proj₂ (proj₂ (surj 𝑴))

      -- Inclusion of interval elements reflects to reversed refinement.
      mono-flip : {𝑴 𝑵 : Interval≈} → 𝑴 ≤ᵢ 𝑵 → part 𝑵 ⊑ part 𝑴
      mono-flip {𝑴} {𝑵} le =
        K-reflects s s≉ε {pu = part 𝑵} {pw = part 𝑴}
          (λ k → part-in 𝑵 (le (part-out 𝑴 k)))

    kurzweilIntervalIso : IntervalIso Sⁿ Diag Diag-isSubgroup (dualLattice (EqLattice n))
    kurzweilIntervalIso = record
      { to         = part
      ; from       = toInterval
      ; to-mono    = λ {𝑴} {𝑵} le →
          ≤ᵈ-unflip {x = part 𝑴} {y = part 𝑵}
            (⊑→≤ {pu = part 𝑵} {pw = part 𝑴} (mono-flip {𝑴} {𝑵} le))
      ; from-mono  = λ {pu} {pw} le →
          K-antitone {pu = pw} {pw = pu}
            (≤→⊑ {pu = pw} {pw = pu} (≤ᵈ-flip {x = pu} {y = pw} le))
      ; to∘from    = λ pv →
          K-injective s s≉ε {pu = part (toInterval pv)} {pw = pv}
            (part-in (toInterval pv)) (part-out (toInterval pv))
      ; from∘to    = λ 𝑴 → part-out 𝑴 , part-in 𝑴
      }
```

The form RP-4's wreath no-go consumes: the dual of the partition lattice is
group representable, witnessed on `[D , Sⁿ]`.

```agda
    -- Corollary: Eq(n)′ is group representable.
    eqDual-groupRepresentable : GroupRepresentable (dualLattice (EqLattice n))
    eqDual-groupRepresentable = record
      { grp           = Sⁿ
      ; sub           = Diag
      ; isSubgroup    = Diag-isSubgroup
      ; interval-iso  = kurzweilIntervalIso
      }
```

#### Consumer interface checks

The signatures the two consumers will call, stated (not proved) so that a
mismatch surfaces here rather than in their branches.  The Kurzweil–Netter proof
(issue #502) composes the WP-3 bridge `Con (Sⁿ ↷ Sⁿ/D) ≅ [D , Sⁿ]` of
[FLRP.Bridge][] with `kurzweilIntervalIso`{.AgdaFunction}; its target is
therefore a `ConIso`{.AgdaFunction} between the coset algebra at the diagonal
and the dual partition lattice.  RP-4 (issue #461) consumes
`eqDual-groupRepresentable`{.AgdaFunction} directly, at a nonabelian simple
instantiation of `𝒮`.

```agda
module ConsumerChecks (𝒮 : Group 0ℓ 0ℓ) (n : ℕ) where

  open KurzweilInterval 𝒮 n

  open CosetAction Sⁿ Diag Diag-isSubgroup using ( cosetAlgebra )

  -- #502 will inhabit this by composing the WP-3 bridge with kurzweilIntervalIso.
  DualityConIso : Type (lsuc 0ℓ)
  DualityConIso = ConIso cosetAlgebra (dualLattice (EqLattice n))
```
