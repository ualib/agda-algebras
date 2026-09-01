---
layout: default
file: "src/FLRP/KurzweilInterval.lagda.md"
title: "FLRP.KurzweilInterval module (The Agda Universal Algebra Library)"
date: "2026-07-27"
author: "the agda-algebras development team"
---

### Kurzweil's interval `[D , Sⁿ] ≅ Eq(n)′`

This is the [FLRP.KurzweilInterval][] module of the [Agda Universal Algebra Library][].

This module packages the group infrastructure of

+ the power `Sⁿ`{.AgdaFunction},
+ the diagonal subgroup `D`{.AgdaFunction} of `Sⁿ`{.AgdaFunction}, and
+ the partition subgroups `K_π`,

into the interval presentation the FLRP research program consumes.

The package consists of the subgroup lattice interval `[D , Sⁿ]`, as an
`UpperInterval`{.AgdaModule} instance of [FLRP.Enforceable][], and
**Kurzweil's lemma** asserting that the interval is isomorphic to the dual of the
partition lattice `Eq(n)` as an `IntervalIso`{.AgdaFunction}.

The classical statement (Kurzweil 1985) splits into two halves of very different
characters, and the formal treatment mirrors the split honestly:[^1]

+  **The dual order embedding is proved outright**.  `π ↦ K_π` lands in the
   interval, reverses the refinement order in both directions, and is injective
   up to kernel equality; this is the content the written sources actually
   prove, it is finite combinatorics, and it needs only a *nontrivial* base
   group ([Classical.Structures.Group.PartitionSubgroup][]).

+  **Surjectivity is a registered hypothesis**.  That every respecting subgroup
   between `D` and `Sⁿ` is a partition subgroup is the half where `S` must be a
   finite nonabelian simple group; the sources cite it to Kurzweil's article
   without reproof, and its formalization needs the normal-subgroup structure
   theory of powers of a simple group (subdirect products, block inductions) that
   the library does not yet have.  Per the `--safe` discipline it enters as the
   explicit hypothesis `KurzweilSurjectivity`{.AgdaFunction}, registered as
   **Entry 4** of [FLRP.Assumptions][]; it is stated in the Σ-form that
   *hands the consumer the partition witness*, which is exactly what the
   isomorphism's inverse map needs.  The Σ-form now comes in two layers: over
   semantic interval elements (`KurzweilSurjectivity`{.AgdaFunction}, the
   classical statement of record) and over decidable ones
   (`KurzweilSurjectivityᵈ`{.AgdaFunction}, the working form the
   Kurzweil–Netter route consumes).  The split is forced, not stylistic: the
   closing theorem of this module shows the Layer-S form implies full excluded
   middle at level zero, so the retirement of Entry 4, proving surjectivity
   for a nonabelian simple base, can only ever land on the decidable form.

Given the hypothesis, `kurzweilIntervalIso`{.AgdaFunction} is a theorem:
`[D , Sⁿ] ≅ (Eq n)′` in the `IntervalIso` presentation, with the dual order
handled by `≤ᵈ-flip`{.AgdaFunction} / `≤ᵈ-unflip`{.AgdaFunction} of
[Classical.Structures.Lattice.Dual][] and the refinement order bridged to the
lattice meet order by `⊑→≤`{.AgdaFunction} / `≤→⊑`{.AgdaFunction}.  The corollary
`eqDual-groupRepresentable`{.AgdaFunction}, asserting that the dual partition
lattice is group representable, is the form RP-4's wreath "no go" consumes, and
the consumer-interface module at the bottom records the composite signature the
Kurzweil–Netter duality proof will call.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.KurzweilInterval where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty        using ( ⊥-elim )
open import Data.Fin.Patterns using ( 0F ; 1F )
open import Data.Fin.Properties using ( _≟_ )
open import Data.Nat.Base     using ( ℕ )
open import Data.Product      using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base     using ( _⊎_ ; inj₁ ; inj₂ )
open import Level             using ( 0ℓ ) renaming ( suc to lsuc )
open import Relation.Binary   using ( Setoid )
open import Relation.Binary.Definitions using ( _Respects_ )
open import Relation.Binary.PropositionalEquality as ≡ using ()
open import Relation.Nullary  using ( ¬_ ; Dec ; yes ; no )
open import Relation.Unary    using ( Pred ; _∈_ ; _⊆_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Group.Basic             using  ( Group
                                                                ; module Group-Op )
open import Classical.Structures.Group.GSet              using  ( module CosetAction )
open import Classical.Signatures.Group                   using  ( ∙-Op ; ⁻¹-Op )
open import Classical.Structures.Group.PartitionSubgroup using  ( module PartitionSubgroups )
open import Classical.Structures.Group.Subgroups         using  ( mkIsSubgroup )
open import Classical.Structures.Interpret               using  ( interp-cong )
open import Classical.Structures.Lattice.Dual            using  ( module LatticeDual
                                                                ; dualLattice )
open import Classical.Structures.Lattice.Partitions      using  ( EqLattice ; SameBlock
                                                                ; _⊑_ ; ⊑→≤ ; ≤→⊑ )
open import FLRP.Enforceable                             using  ( module UpperInterval
                                                                ; IntervalIso
                                                                ; GroupRepresentable )
open import FLRP.Problem                                 using  ( ConIso ; EM₀ ; WLEM₀
                                                                ; EM₀→WLEM₀ )
open import Setoid.Algebras                              using  ( 𝕌[_] ; 𝔻[_] ; Algebra)
open import Setoid.Congruences.Certificates.Schema       using  ( ParentVec ; parent )
```
-->

#### The interval `[D , Sⁿ]` and the surjectivity hypothesis

`KurzweilInterval`{.AgdaModule}` 𝒮 n` fixes the base group and the exponent,
instantiates the partition-subgroup toolkit, and opens the upper interval at the
diagonal.

```agda
module KurzweilInterval (𝒮@(𝑺 , _) : Group 0ℓ 0ℓ) (n : ℕ) where

  open Setoid 𝔻[ 𝑺 ] using ( _≈_ )
  open Group-Op 𝒮 using ( ε )
  open PartitionSubgroups n 𝒮 public

  -- The power 𝑺ⁿ (the ⨅ᵍ-Group of the opened toolkit, named for readability).
  𝑺ⁿ : Group 0ℓ 0ℓ
  𝑺ⁿ = ⨅ᵍ-Group
  Sⁿ : Algebra 0ℓ 0ℓ
  Sⁿ = 𝑺ⁿ .proj₁
  open UpperInterval 𝑺ⁿ Diag Diag-isSubgroup public

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

The definition above quantifies over *semantic* interval elements.  Its Layer-D
sibling quantifies instead over the decidable interval elements
`Intervalᵈ`{.AgdaFunction} of [FLRP.Enforceable][]: the same Σ-form, taken over
elements that carry a membership decider.  This is the form the Kurzweil–Netter
route consumes, because every interval element it manipulates is the base-coset
class of a *decidable* congruence, and it is the form whose proof for a finite
nonabelian simple base group retires Entry 4; the closing theorem of this
module shows the Layer-S form above is not provable at all.

```agda
  -- Kurzweil surjectivity, Layer-D form: the partition witness over interval
  -- elements carrying a membership decider.
  KurzweilSurjectivityᵈ : Type (lsuc 0ℓ)
  KurzweilSurjectivityᵈ =
    (𝑴 : Intervalᵈ) → Σ[ pv ∈ ParentVec n ] ((set (𝑴 .proj₁) ⊆ K pv) × (K pv ⊆ set (𝑴 .proj₁)))
```

Forgetting the decider restricts the Layer-S form to the decidable instances,
so the classical statement of record implies the working form; nothing runs the
other way constructively, and the closing theorem prices the gap exactly.

```agda
  -- The Layer-S form restricts to the decidable instances.
  surjectivity→surjectivityᵈ : KurzweilSurjectivity → KurzweilSurjectivityᵈ
  surjectivity→surjectivityᵈ surj 𝑴 = surj (𝑴 .proj₁)
```

#### The interval isomorphism `[D , Sⁿ] ≅ Eq(n)′`

Under the surjectivity hypothesis and a nontriviality witness for the base
group, `π ↦ K_π` and the produced partitions are a mutually inverse monotone
pair between the interval and the *dual* of `Eq(n)`: order reversal turns the
interval order into the dual lattice order, with the round trips repaired by
order reflection (`K-reflects`{.AgdaFunction}) and injectivity
(`K-injective`{.AgdaFunction}).

```agda
  module _ (s : 𝕌[ 𝑺 ]) (s≉ε : ¬ s ≈ ε) (surj : KurzweilSurjectivity)
    where

    open LatticeDual (EqLattice n) using ( ≤ᵈ-flip ; ≤ᵈ-unflip )

    private
      -- The partition attached to an interval element by the hypothesis.
      part : Interval≈ → ParentVec n
      part 𝑴 = surj 𝑴 .proj₁

      part-in : (𝑴 : Interval≈) → set 𝑴 ⊆ K (part 𝑴)
      part-in 𝑴 = surj 𝑴 .proj₂ .proj₁

      part-out : (𝑴 : Interval≈) → K (part 𝑴) ⊆ set 𝑴
      part-out 𝑴 = surj 𝑴 .proj₂ .proj₂

      -- Inclusion of interval elements reflects to reversed refinement.
      mono-flip : {𝑴 𝑵 : Interval≈} → 𝑴 ≤ᵢ 𝑵 → part 𝑵 ⊑ part 𝑴
      mono-flip {𝑴} {𝑵} le =
        K-reflects s s≉ε {pu = part 𝑵} {pw = part 𝑴}
          λ k → part-in 𝑵 (le (part-out 𝑴 k))

    kurzweilIntervalIso : IntervalIso 𝑺ⁿ Diag Diag-isSubgroup (dualLattice (EqLattice n))
    kurzweilIntervalIso = record
      { to         = part
      ; from       = toInterval
      ; to-mono    = λ {𝑴} {𝑵} le → ≤ᵈ-unflip ( ⊑→≤ {pu = part 𝑵} {pw = part 𝑴}
                                                   ( mono-flip {𝑴} {𝑵} le ) )
      ; from-mono  = λ {pu} {pw} le → K-antitone {pu = pw} {pw = pu}
                                        ( ≤→⊑ (≤ᵈ-flip {x = pu} {y = pw} le) )
      ; to∘from    = λ pv → K-injective s s≉ε {pu = part (toInterval pv)} {pw = pv}
                              ( part-in (toInterval pv)) (part-out (toInterval pv) )
      ; from∘to    = λ 𝑴 → part-out 𝑴 , part-in 𝑴
      }
```

**The form RP-4's wreath "no go" consumes**.  The dual of the partition lattice is
group representable, witnessed on `[D , Sⁿ]`.

```agda
    -- Corollary: Eq(n)′ is group representable.
    eqDual-groupRepresentable : GroupRepresentable (dualLattice (EqLattice n))
    eqDual-groupRepresentable = record
      { grp           = 𝑺ⁿ
      ; sub           = Diag
      ; isSubgroup    = Diag-isSubgroup
      ; interval-iso  = kurzweilIntervalIso
      }
```

#### The Layer-S form is excluded middle

The Σ-form of `KurzweilSurjectivity`{.AgdaFunction} produces the partition as
concrete data from an *arbitrary* respecting interval element, and interval
elements can encode arbitrary propositions in their membership predicates (the
observation footnoted at `Intervalᵈ`{.AgdaFunction} in [FLRP.Enforceable][]).
The two collide: producing discrete data from an oracle element decides the
proposition it encodes.  This is the oracle-congruence obstruction of
[FLRP.Problem][] in interval clothing, with one sharpening: it prices the full
Layer-S statement rather than any particular representation, and it lands on
the strong formula `EM₀`{.AgdaFunction} rather than `WLEM₀`{.AgdaFunction}.

The construction needs only the exponent `2` and an apartness witness in the
base group.  For a proposition `P`, the **oracle subgroup** relates the two
coordinates *or* asserts `P`.  It respects the pointwise equality and is closed
under the power operations because the right branch of the disjunction is
absorbing, and it contains the diagonal through the left branch.  Where the
produced partition puts the two indices is decidable, and either answer
decides `P`: if they share a block, the containment `U ⊆ K pv` evaluated at
the probe tuple `(ε , s₀)` under hypothesis `P` forces `ε ≈ s₀`, refuting
`P`; if they do not, the probe lies in `K pv` outright, and the other
containment hands over `(ε ≈ s₀) ⊎ P` with the left branch absurd.

```agda
module _ (𝒮@(𝑺 , _)  : Group 0ℓ 0ℓ)  (open Setoid 𝔻[ 𝑺 ] using ( _≈_ ))
                                      (open Group-Op 𝒮 using ( ε ))
         (s₀          : 𝕌[ 𝑺 ])
         (s₀≉ε        : ¬ s₀ ≈ ε)
  where

  open KurzweilInterval 𝒮 2
  open Setoid 𝔻[ 𝑺 ]  using () renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open Setoid 𝔻[ Sⁿ ] using () renaming ( _≈_ to _≈ₚ_ )
  open Group-Op 𝑺ⁿ    using () renaming ( _∙_ to _∙ₚ_ ; ε to εₚ ; _⁻¹ to _⁻¹ₚ )

  -- Kurzweil surjectivity at Layer S decides every level-zero proposition.
  kurzweilSurjectivity→EM : KurzweilSurjectivity → EM₀
  kurzweilSurjectivity→EM surj P = decide (parent pv 0F ≟ parent pv 1F)
    where
    -- The oracle subgroup: the two coordinates agree, or P holds.
    U : Pred 𝕌[ Sⁿ ] 0ℓ
    U u = (u 0F ≈ u 1F) ⊎ P

    U-respects : U Respects _≈ₚ_
    U-respects e (inj₁ q)  = inj₁ (≈trans (≈sym (e 0F)) (≈trans q (e 1F)))
    U-respects e (inj₂ p)  = inj₂ p

    U-∙ : ∀ {x y} → x ∈ U → y ∈ U → (x ∙ₚ y) ∈ U
    U-∙ {x} {y} (inj₁ qx) (inj₁ qy) =
      inj₁ (≈trans  (⊗-pointwise x y 0F)
                    (≈trans  (interp-cong 𝑺 ∙-Op λ { 0F → qx ; 1F → qy })
                             (≈sym (⊗-pointwise x y 1F))))
    U-∙ (inj₁ _)   (inj₂ p) = inj₂ p
    U-∙ (inj₂ p)   _        = inj₂ p

    U-ε : εₚ ∈ U
    U-ε = inj₁ (≈trans (e-pointwise 0F) (≈sym (e-pointwise 1F)))

    U-⁻¹ : ∀ {x} → x ∈ U → (x ⁻¹ₚ) ∈ U
    U-⁻¹ {x} (inj₁ q) =
      inj₁ (≈trans  (inv-pointwise x 0F)
                    (≈trans  (interp-cong 𝑺 ⁻¹-Op λ { 0F → q })
                             (≈sym (inv-pointwise x 1F))))
    U-⁻¹ (inj₂ p) = inj₂ p

    -- The oracle subgroup as an interval element.
    𝑴P : Interval≈
    𝑴P = mk U  (mkIsSubgroup 𝑺ⁿ U-respects
                  (λ {x} {y} → U-∙ {x} {y}) U-ε (λ {x} → U-⁻¹ {x}))
               (λ d → inj₁ (d 0F 1F))

    -- The partition the hypothesis attaches to it, with its two containments.
    pv : ParentVec 2
    pv = surj 𝑴P .proj₁

    U⊆Kpv : U ⊆ K pv
    U⊆Kpv = surj 𝑴P .proj₂ .proj₁

    Kpv⊆U : K pv ⊆ U
    Kpv⊆U = surj 𝑴P .proj₂ .proj₂

    -- The probe tuple (ε , s₀).
    w : 𝕌[ Sⁿ ]
    w 0F = ε
    w 1F = s₀

    decide : Dec (SameBlock pv 0F 1F) → P ⊎ ¬ P
    decide (yes sb) = inj₂ (λ p → s₀≉ε (≈sym (U⊆Kpv {w} (inj₂ p) {0F} {1F} sb)))
    decide (no ¬e)  = fromU (Kpv⊆U {w} w∈K)
      where
      w∈K : w ∈ K pv
      w∈K {0F} {0F} _   = ≈refl
      w∈K {0F} {1F} sb  = ⊥-elim (¬e sb)
      w∈K {1F} {0F} sb  = ⊥-elim (¬e (≡.sym sb))
      w∈K {1F} {1F} _   = ≈refl

      fromU : w ∈ U → P ⊎ ¬ P
      fromU (inj₁ e)  = ⊥-elim (s₀≉ε (≈sym e))
      fromU (inj₂ p)  = inj₁ p
```

Through the generic weakening of [FLRP.Problem][], the theorem places the
Layer-S form at or above every obstruction of `WLEM₀`{.AgdaFunction} strength
in that module's no-go family.

```agda
  -- The weak form, for comparison with the chain₂ no-go family.
  kurzweilSurjectivity→WLEM : KurzweilSurjectivity → WLEM₀
  kurzweilSurjectivity→WLEM surj = EM₀→WLEM₀ (kurzweilSurjectivity→EM surj)
```

#### Consumer interface checks

**The signatures the two consumers will call**.  This is stated (not proved) so
that a mismatch surfaces here rather than in their branches.

The Kurzweil–Netter proof composes the WP-3 bridge `Con (Sⁿ ↷ Sⁿ/D) ≅ [D , Sⁿ]` of
[FLRP.Bridge][] with `kurzweilIntervalIso`{.AgdaFunction}; its target is therefore
a `ConIso`{.AgdaFunction} between the coset algebra at the diagonal and the dual
partition lattice.  RP-4 consumes `eqDual-groupRepresentable`{.AgdaFunction}
directly, at a nonabelian simple instantiation of `𝒮`.

```agda
module ConsumerChecks (𝒮 : Group 0ℓ 0ℓ) (n : ℕ) where
  open KurzweilInterval 𝒮 n
  open CosetAction 𝑺ⁿ Diag Diag-isSubgroup using ( cosetAlgebra )

  -- The Kurzweil-etter proof inhabits this by composing the WP-3 bridge with
  -- kurzweilIntervalIso.
  DualityConIso : Type (lsuc 0ℓ)
  DualityConIso = ConIso cosetAlgebra (dualLattice (EqLattice n))
```

---

[^1]: See also `docs/papers/fin-lat-rep/SmallLatticeReps.tex` (`lem:latt-duals`)
      and DeMeo's thesis § 2.2.
