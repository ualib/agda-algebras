---
layout: default
file: "src/Classical/Structures/Group/MinimalNormalDescent.lagda.md"
title: "Classical.Structures.Group.MinimalNormalDescent module"
date: "2026-08-17"
author: "the agda-algebras development team"
---

### Minimal normal subgroups of a finite group

This is the [Classical.Structures.Group.MinimalNormalDescent][] module of the [Agda Universal Algebra Library][].

Every nontrivial normal subgroup of a finite group contains a **minimal** one.  This
module proves it, by well-founded descent on the order of a subgroup, and locates
exactly the classical content of the textbook statement.

The textbook argument is a one-liner: among the nontrivial normal subgroups contained
in `N`{.AgdaBound} choose one of least order.  Mechanized constructively, two things
have to be settled first, and they are the two design decisions of the module.

+  **What is the order of a subgroup?**  A `FiniteAlgebra`{.AgdaRecord} witness
   ([Setoid.Algebras.Finite][]) for the underlying algebra gives decidable setoid
   equality and a surjective enumeration `enum : Fin card → G`, so the order of a
   subgroup is the number of enumerated elements it contains — provided membership can
   be *tested*.  A semantic-only subgroup has no computable order, so the measure lives
   on the Layer-D presentation `Normalᵈ`{.AgdaFunction}: a normal subgroup bundled with
   a membership decision procedure, exactly as `Intervalᵈ`{.AgdaFunction} of
   [FLRP.Enforceable][] bundles an interval element with one.  This is [ADR-008][]'s
   discipline, stated rather than smuggled in.

+  **Which nontriviality?**  `Nontrivial N`{.AgdaFunction} of
   [Classical.Structures.Group.MinimalNormal][] is the negative statement `¬ (N ⊆ 1)`,
   which carries no witness — and a descent has nothing to descend from without one.
   The theorem is therefore proved with `Witnessed`{.AgdaFunction} nontriviality on
   both sides, and the two are reconciled where they can be: on a *decidably presented*
   subgroup of a finite group the witness is recovered by a finite search
   (`witness`{.AgdaFunction}).  The unrestricted passage is not available, and that is
   a theorem, not an omission — see the no-go below.

#### What is proved

`minimal-normal-descentʷ`{.AgdaFunction} is the theorem: a decidably presented normal
subgroup with a witness contains a decidably presented `IsMinimalNormalʷ`{.AgdaRecord}
one.  Note what is *not* restricted: the minimality clause it delivers quantifies over
**every** normal subgroup, with no decidability assumed of it, and only the
nontriviality hypothesis is in witnessed form.  The Layer-D corollaries follow by the
finite search: `minimal-normal-descentᵈ`{.AgdaFunction} takes the negative
nontriviality hypothesis, and `minimalʷ→minimalᵈ`{.AgdaFunction} discharges the
negative one in the minimality clause for a decidably presented competitor.

The engine is [Classical.Structures.Group.NormalClosure][].  Descent needs a *smaller*
candidate, and the normal closure `⟪ y ⟫`{.AgdaFunction} of an element supplies it: at
each stage the argument asks whether some enumerated non-identity member of the current
subgroup generates a strictly smaller normal subgroup.  If one does, recurse into it;
if none does, the current subgroup is minimal, because a competitor's *witness*
generates a normal closure trapped between them, and the failed search says that
closure is not smaller — so it is all of the current subgroup, which is therefore
inside the competitor.  Nothing here needs to enumerate the normal subgroups of the
group; the search ranges over its *elements*, which is what carrier finiteness gives.

#### The no-go, and what it means for the FLRP program

`MinimalNormalDescent`{.AgdaFunction} of [FLRP.Reductions][] — the hypothesis threaded
through Entries 1–3 of the RP-2 enforcement catalog — asks for a minimal normal
subgroup in the *unrestricted* sense: minimality against every normal subgroup whose
nontriviality is the negative statement.  `minimal→DNE`{.AgdaFunction} shows that the
*witnessed* reading of that demand is not merely harder to prove, but classical: an
unrestricted-minimal normal subgroup of a finite group, taken together with a
witnessed non-identity element, decides `¬ ¬ P → P` for every proposition
`P`{.AgdaBound} at the working level.  The instrument is the normal subgroup
`M ∩ (1 ∪ P)`{.AgdaFunction}, an "oracle subgroup" in the style of the oracle
congruence `θ[ P ]`{.AgdaFunction} that drives the WP-1 no-go of [FLRP.Problem][].
The witness hypothesis is doing real work in that statement — extracting an element
from the negative `Nontrivial`{.AgdaFunction} is itself a classical step
(`witnessing→DNE`{.AgdaFunction} below) — so what the no-go rules out is any proof
of descent that returns its minimal subgroups in witnessed form, which is the form
the construction here naturally produces and the form every catalog consumer uses.
Whether the bare negative reading of the hypothesis is *independently* derivable is
not settled by this no-go; no route to it is in sight, and it would not feed the
witnessed consumers in any case.

So the witnessed route to the descent hypothesis cannot be discharged outright, and
the Layer-D restriction above is forced for it.  What *is* available unconditionally
is the witnessed form over decidably presented subgroups, which is
strictly stronger than the Layer-D form and is what a consumer with decidably presented
subgroups actually needs; `minimal-normal-descent`{.AgdaFunction} records the remaining
gap as one named principle, `WitnessedNontriviality`{.AgdaFunction}, rather than
leaving it distributed over the catalog entries.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.MinimalNormalDescent where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                  using  ( ⊥-elim )
open import Data.Fin.Base               using  ( Fin )
open import Data.Fin.Properties         using  ( any? )
open import Data.List.Base              using  ( allFin ; filter ; length )
open import Data.Nat.Base               using  ( ℕ ; _≤_ ; _<_ )
open import Data.Nat.Induction          using  ( <-wellFounded )
open import Data.Nat.Properties         using  ( _<?_ )
open import Data.Product                using  ( _×_ ; _,_ ; Σ-syntax ; proj₁ ; proj₂ )
open import Data.Sum.Base               using  ( _⊎_ ; inj₁ ; inj₂ )
open import Induction.WellFounded       using  ( Acc ; acc )
open import Level                       using  ( Level ; _⊔_ ) renaming ( suc to lsuc )
open import Relation.Binary             using  ( Setoid )
open import Relation.Nullary            using  ( ¬_ ; Dec ; yes ; no )
open import Relation.Nullary.Decidable  using  ( ¬? ; _×-dec_ ; decidable-stable )
open import Relation.Unary              using  ( Pred ; _∈_ ; _⊆_ ; _∩_ )

open import Data.List.Membership.Propositional.Properties  using  ( ∈-allFin )

import Algebra.Properties.Group as GroupProperties

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Overture                                     using  ( filter-length-mono
                                                                ; filter-length-strict )
open import Classical.Bundles.Group                      using  ( ⟨_⟩ᵍᵖ )
open import Classical.Structures.Group.Basic             using  ( Group ; module Group-Op )
open import Classical.Structures.Group.Congruences        using  ( module GroupCongruences )
open import Classical.Structures.Group.Conjugation        using  ( module Conjugate )
open import Classical.Structures.Group.MinimalNormal      using  ( module MinimalNormal )
open import Classical.Structures.Group.NormalClosure      using  ( module NormalClosureᵈ )
open import Classical.Structures.Group.Subgroups          using  ( IsSubgroup
                                                                 ; mkIsSubgroup )
open import Setoid.Algebras.Basic                        using  ( 𝕌[_] ; 𝔻[_] )
open import Setoid.Algebras.Finite                       using  ( FiniteAlgebra )
```
-->

#### The finiteness interface

A **finite group** is a group together with carrier-finiteness data for its underlying
algebra.  Nothing else is assumed: no enumeration of the subgroups, and no finiteness
datum about the congruence lattice.

```agda
module MinimalNormalDescent {α ρ : Level} (𝒢 : Group α ρ) (𝑭 : FiniteAlgebra (proj₁ 𝒢)) where
  private
    𝑮 = proj₁ 𝒢
    G = 𝕌[ 𝑮 ]

  open FiniteAlgebra 𝑭  using  ( _≟_ ; card ; enum ; enum-sur )
  open Setoid 𝔻[ 𝑮 ]  using  ( _≈_ )
                      renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open Group-Op 𝒢               using  ( _∙_ ; ε ; _⁻¹ ; ∙-cong ; ⁻¹-cong ; idˡ-law )
  open GroupProperties ⟨ 𝒢 ⟩ᵍᵖ  using  ( ε⁻¹≈ε )
  open Conjugate 𝒢              using  ( IsNormal ; conj-cong ; conj-ε )
  open GroupCongruences 𝒢       using  ( NormalSubgroup ; set ; set-isSubgroup
                                       ; set-normal )
  open NormalClosureᵈ 𝒢 𝑭       using  ( L ; ⟪_⟫ ; ⟪⟫-dec ; ⟪⟫-mem ; ⟪⟫-least )
  open MinimalNormal 𝒢 ρ        public
```

Passing between the two bundlings of a normal subgroup — the record
`IsNormalSubgroup`{.AgdaRecord} of [Classical.Structures.Group.MinimalNormal][], and
the Σ-type `NormalSubgroup`{.AgdaFunction} of
[Classical.Structures.Group.Congruences][] that the normal closure speaks — is
projection and pairing.

```agda
  private
    bundle : (N : Pred G L) → IsNormalSubgroup N → NormalSubgroup L
    bundle N N-nsg = N , N-nsg .isSubgroup , N-nsg .isNormal

    unbundle : (𝑵 : NormalSubgroup L) → IsNormalSubgroup (set 𝑵)
    unbundle 𝑵 = record  { isSubgroup  = set-isSubgroup 𝑵
                         ; isNormal    = set-normal 𝑵 }
```

#### Layer D: normal subgroups that can be counted

```agda
  -- A normal subgroup together with a decision procedure for its membership.
  Normalᵈ : Type (α ⊔ ρ ⊔ lsuc L)
  Normalᵈ = Σ[ N ∈ Pred G L ] (IsNormalSubgroup N × ((x : G) → Dec (x ∈ N)))

  -- Its three components.
  setᵈ : Normalᵈ → Pred G L
  setᵈ = proj₁

  isNormalᵈ : (𝑵 : Normalᵈ) → IsNormalSubgroup (setᵈ 𝑵)
  isNormalᵈ 𝑵 = proj₁ (proj₂ 𝑵)

  infix 4 _∈ᵈ?_

  _∈ᵈ?_ : (x : G) (𝑵 : Normalᵈ) → Dec (x ∈ setᵈ 𝑵)
  x ∈ᵈ? 𝑵 = proj₂ (proj₂ 𝑵) x
```

Two consequences of the enumeration, used throughout: every element has an enumerated
representative, and a subgroup — respecting the setoid equality — contains an element
exactly when it contains that representative.

```agda
  private
    idx : G → Fin card
    idx x = proj₁ (enum-sur x)

    idx-≈ : (x : G) → enum (idx x) ≈ x
    idx-≈ x = proj₂ (enum-sur x)

    respectsᵈ : (𝑵 : Normalᵈ) {x y : G} → x ≈ y → x ∈ setᵈ 𝑵 → y ∈ setᵈ 𝑵
    respectsᵈ 𝑵 = IsSubgroup.respects (isNormalᵈ 𝑵 .isSubgroup)

    -- The enumerated representative of a member is a member ...
    memᵈ-idx : (𝑵 : Normalᵈ){x : G} → x ∈ setᵈ 𝑵 → enum (idx x) ∈ setᵈ 𝑵
    memᵈ-idx 𝑵 {x} x∈N = respectsᵈ 𝑵 (≈sym (idx-≈ x)) x∈N

    -- ... and a non-member's representative is a non-member.
    ¬memᵈ-idx : (𝑵 : Normalᵈ){x : G} → ¬ (x ∈ setᵈ 𝑵) → ¬ (enum (idx x) ∈ setᵈ 𝑵)
    ¬memᵈ-idx 𝑵 {x} x∉N p = x∉N (respectsᵈ 𝑵 (idx-≈ x) p)
```

#### The order of a decidably presented subgroup

```agda
  -- The order of 𝑵: the number of enumerated carrier elements it contains.
  ∥_∥ : Normalᵈ → ℕ
  ∥ 𝑵 ∥ = length (filter (λ i → enum i ∈ᵈ? 𝑵) (allFin card))
```

The two facts the descent runs on, both instances of the counting lemmas of
[Overture.Counting][]: order is monotone under containment, and strictly monotone when
the containment misses an enumerated element.

```agda
  -- A subgroup inside another has no larger order ...
  ∥∥-mono : (𝑴 𝑵 : Normalᵈ) → setᵈ 𝑴 ⊆ setᵈ 𝑵 → ∥ 𝑴 ∥ ≤ ∥ 𝑵 ∥
  ∥∥-mono 𝑴 𝑵 M⊆N =
    filter-length-mono  (λ i → enum i ∈ᵈ? 𝑴) (λ i → enum i ∈ᵈ? 𝑵)
                        (λ {i} → M⊆N) (allFin card)

  -- ... and strictly smaller order if it misses an enumerated element.
  ∥∥-strict : (𝑴 𝑵 : Normalᵈ)(i : Fin card) → setᵈ 𝑴 ⊆ setᵈ 𝑵
    →  enum i ∈ setᵈ 𝑵 → ¬ (enum i ∈ setᵈ 𝑴) → ∥ 𝑴 ∥ < ∥ 𝑵 ∥
  ∥∥-strict 𝑴 𝑵 i M⊆N mem ¬mem =
    filter-length-strict  (λ j → enum j ∈ᵈ? 𝑴) (λ j → enum j ∈ᵈ? 𝑵)
                          (λ {j} → M⊆N) (allFin card) (∈-allFin i) mem ¬mem
```

Contrapositively: a subgroup inside another and of no smaller order is all of it.  The
decision is taken as an argument by a named lemma rather than split on in the proof,
per the library's house style.

```agda
  -- If 𝑵 ⊆ 𝑴 is not of strictly smaller order, then 𝑴 ⊆ 𝑵.
  ¬smaller→above : (𝑴 𝑵 : Normalᵈ) → setᵈ 𝑵 ⊆ setᵈ 𝑴 → ¬ (∥ 𝑵 ∥ < ∥ 𝑴 ∥)
    →  setᵈ 𝑴 ⊆ setᵈ 𝑵
  ¬smaller→above 𝑴 𝑵 N⊆M ¬lt {x} x∈M = decide (enum (idx x) ∈ᵈ? 𝑵)
    where
    decide : Dec (enum (idx x) ∈ setᵈ 𝑵) → x ∈ setᵈ 𝑵
    decide (yes p)  = respectsᵈ 𝑵 (idx-≈ x) p
    decide (no ¬p)  =
      ⊥-elim (¬lt (∥∥-strict 𝑵 𝑴 (idx x) N⊆M (memᵈ-idx 𝑴 x∈M) ¬p))
```

#### Nontriviality is witnessed, at Layer D

```agda
  -- On a finite group a decidably presented nontrivial normal subgroup has a witness.
  witness : (𝑵 : Normalᵈ) → Nontrivial (setᵈ 𝑵) → Witnessed (setᵈ 𝑵)
  witness 𝑵 nontriv = found (any? (λ i → (enum i ∈ᵈ? 𝑵) ×-dec ¬? (enum i ≟ ε)))
    where
    -- Found: the enumerated element is the witness.  Not found: every member of 𝑵
    -- is ≈ ε, since its representative is, so 𝑵 was trivial after all.
    found : Dec (Σ[ i ∈ Fin card ] (enum i ∈ setᵈ 𝑵 × ¬ (enum i ≈ ε)))
          → Witnessed (setᵈ 𝑵)
    found (yes (i , mem , ne))  = enum i , mem , ne
    found (no ¬any)             = ⊥-elim (nontriv triv)
      where
      triv : setᵈ 𝑵 ⊆ Triv
      triv {x} x∈N =
        ≈trans  (≈sym (idx-≈ x))
                (decidable-stable  (enum (idx x) ≟ ε)
                                   (λ ne → ¬any (idx x , memᵈ-idx 𝑵 x∈N , ne)))
```

#### The descent

The normal closure of an element, as a Layer-D normal subgroup — the candidate the
descent steps into.

```agda
  -- The normal closure of y, decidably presented.
  ⟪_⟫ᵈ : G → Normalᵈ
  ⟪ y ⟫ᵈ = set ⟪ y ⟫ , unbundle ⟪ y ⟫ , ⟪⟫-dec y

  -- It sits inside every normal subgroup containing y, decidably presented or not.
  ⟪⟫ᵈ-least : (y : G)(N : Pred G L) → IsNormalSubgroup N → y ∈ N → setᵈ ⟪ y ⟫ᵈ ⊆ N
  ⟪⟫ᵈ-least y N N-nsg = ⟪⟫-least y (bundle N N-nsg)
```

One step of the descent is the question: does some enumerated non-identity member of
`𝑴`{.AgdaBound} generate a strictly smaller normal subgroup?  It is decidable, being a
finite search over the carrier enumeration.

```agda
  -- The descent step, as a decidable predicate on the carrier enumeration.
  Step : Normalᵈ → Fin card → Type (α ⊔ ρ ⊔ L)
  Step 𝑴 i = (enum i ∈ setᵈ 𝑴) × ¬ (enum i ≈ ε) × (∥ ⟪ enum i ⟫ᵈ ∥ < ∥ 𝑴 ∥)

  Step? : (𝑴 : Normalᵈ)(i : Fin card) → Dec (Step 𝑴 i)
  Step? 𝑴 i =  (enum i ∈ᵈ? 𝑴)
               ×-dec (¬? (enum i ≟ ε) ×-dec (∥ ⟪ enum i ⟫ᵈ ∥ <? ∥ 𝑴 ∥))
```

When the search fails, the current subgroup is minimal.  A competitor `N`{.AgdaBound}
inside it has a witness `y`{.AgdaBound}; the normal closure of `y`{.AgdaBound} lies
inside `N`{.AgdaBound}, hence inside `𝑴`{.AgdaBound}, and the failed search says it is
not of strictly smaller order — so it is all of `𝑴`{.AgdaBound}, and `𝑴 ⊆ N`.

```agda
  -- The minimality of a subgroup no enumerated element of which descends.
  private
    exhausted→minimalʷ : (𝑴 : Normalᵈ) → Witnessed (setᵈ 𝑴)
      →  ((i : Fin card) → ¬ Step 𝑴 i) → IsMinimalNormalʷ (setᵈ 𝑴)
    exhausted→minimalʷ 𝑴 wit ¬step = record
      { normalSubgroupʷ  = isNormalᵈ 𝑴
      ; witnessedʷ       = wit
      ; minimalʷ         = below
      }
      where
      below : (N : Pred G L) → IsNormalSubgroup N → N ⊆ setᵈ 𝑴 → Witnessed N
        →  setᵈ 𝑴 ⊆ N
      below N N-nsg N⊆M (y , y∈N , y≉ε) = λ z → clo⊆N (M⊆clo z)
        where
        i : Fin card
        i = idx y

        -- The witness has an enumerated representative, still a non-identity member.
        i∈N : enum i ∈ N
        i∈N = IsSubgroup.respects (N-nsg .isSubgroup) (≈sym (idx-≈ y)) y∈N

        i≉ε : ¬ (enum i ≈ ε)
        i≉ε e = y≉ε (≈trans (≈sym (idx-≈ y)) e)

        clo⊆N : setᵈ ⟪ enum i ⟫ᵈ ⊆ N
        clo⊆N = ⟪⟫ᵈ-least (enum i) N N-nsg i∈N

        clo⊆M : setᵈ ⟪ enum i ⟫ᵈ ⊆ setᵈ 𝑴
        clo⊆M = ⟪⟫ᵈ-least (enum i) (setᵈ 𝑴) (isNormalᵈ 𝑴) (N⊆M i∈N)

        M⊆clo : setᵈ 𝑴 ⊆ setᵈ ⟪ enum i ⟫ᵈ
        M⊆clo = ¬smaller→above  𝑴 ⟪ enum i ⟫ᵈ clo⊆M
                                (λ lt → ¬step i (N⊆M i∈N , i≉ε , lt))
```

The recursion itself, on the accessibility of the order.  Each step either exhausts the
search — and stops — or moves to a normal closure of strictly smaller order.

```agda
  private
    descend : (𝑴 : Normalᵈ) → Acc _<_ ∥ 𝑴 ∥ → Witnessed (setᵈ 𝑴)
      →  Σ[ 𝑵 ∈ Normalᵈ ] (IsMinimalNormalʷ (setᵈ 𝑵) × setᵈ 𝑵 ⊆ setᵈ 𝑴)
    descend 𝑴 (acc rs) wit = step (any? (Step? 𝑴))
      where
      step : Dec (Σ[ i ∈ Fin card ] Step 𝑴 i)
        →  Σ[ 𝑵 ∈ Normalᵈ ] (IsMinimalNormalʷ (setᵈ 𝑵) × setᵈ 𝑵 ⊆ setᵈ 𝑴)
      step (no ¬any) =
        𝑴 , exhausted→minimalʷ 𝑴 wit (λ i s → ¬any (i , s)) , (λ z → z)
      step (yes (i , i∈M , i≉ε , smaller)) =
        proj₁ inner , proj₁ (proj₂ inner) , (λ z → clo⊆M (proj₂ (proj₂ inner) z))
        where
        clo⊆M : setᵈ ⟪ enum i ⟫ᵈ ⊆ setᵈ 𝑴
        clo⊆M = ⟪⟫ᵈ-least (enum i) (setᵈ 𝑴) (isNormalᵈ 𝑴) i∈M

        inner : Σ[ 𝑵 ∈ Normalᵈ ] (IsMinimalNormalʷ (setᵈ 𝑵) × setᵈ 𝑵 ⊆ setᵈ ⟪ enum i ⟫ᵈ)
        inner = descend  ⟪ enum i ⟫ᵈ (rs smaller)
                         (enum i , ⟪⟫-mem (enum i) , i≉ε)
```

#### The theorem

```agda
  -- Minimal-normal descent: every witnessed-nontrivial, decidably presented normal
  -- subgroup of a finite group contains a minimal normal subgroup.
  minimal-normal-descentʷ : (𝑴 : Normalᵈ) → Witnessed (setᵈ 𝑴)
    →  Σ[ 𝑵 ∈ Normalᵈ ] (IsMinimalNormalʷ (setᵈ 𝑵) × setᵈ 𝑵 ⊆ setᵈ 𝑴)
  minimal-normal-descentʷ 𝑴 = descend 𝑴 (<-wellFounded ∥ 𝑴 ∥)

  -- The same, with nontriviality in its negative form: at Layer D the witness is
  -- recovered by a finite search.
  minimal-normal-descentᵈ : (𝑴 : Normalᵈ) → Nontrivial (setᵈ 𝑴)
    →  Σ[ 𝑵 ∈ Normalᵈ ] (IsMinimalNormalʷ (setᵈ 𝑵) × setᵈ 𝑵 ⊆ setᵈ 𝑴)
  minimal-normal-descentᵈ 𝑴 nontriv = minimal-normal-descentʷ 𝑴 (witness 𝑴 nontriv)

  -- Minimality against a decidably presented competitor, with its nontriviality in
  -- the negative form: the Layer-D reading of `IsMinimalNormal.minimal`.
  minimalʷ→minimalᵈ : {M : Pred G L} → IsMinimalNormalʷ M
    →  (𝑵 : Normalᵈ) → setᵈ 𝑵 ⊆ M → Nontrivial (setᵈ 𝑵) → M ⊆ setᵈ 𝑵
  minimalʷ→minimalᵈ M-min 𝑵 N⊆M nontriv =
    M-min .minimalʷ (setᵈ 𝑵) (isNormalᵈ 𝑵) N⊆M (witness 𝑵 nontriv)
```

#### The no-go: unrestricted minimality is classical

The oracle subgroup.  For a proposition `P`{.AgdaBound}, the elements that are trivial
*or* make `P`{.AgdaBound} true form a normal subgroup: every closure law is satisfied
either by the trivial branch or, once `P`{.AgdaBound} holds, by the constant one.

```agda
  module Oracle (P : Type L) where

    -- The oracle subgroup: the trivial subgroup, inflated by P.
    Trivᴾ : Pred G L
    Trivᴾ x = (x ≈ ε) ⊎ P

    private
      respᴾ : {x y : G} → x ≈ y → Trivᴾ x → Trivᴾ y
      respᴾ x≈y (inj₁ x≈ε)  = inj₁ (≈trans (≈sym x≈y) x≈ε)
      respᴾ _   (inj₂ p)    = inj₂ p

      ∙ᴾ : {x y : G} → Trivᴾ x → Trivᴾ y → Trivᴾ (x ∙ y)
      ∙ᴾ (inj₁ x≈ε)  (inj₁ y≈ε)  = inj₁ (≈trans (∙-cong x≈ε y≈ε) (idˡ-law ε))
      ∙ᴾ (inj₁ _)    (inj₂ p)    = inj₂ p
      ∙ᴾ (inj₂ p)    (inj₁ _)    = inj₂ p
      ∙ᴾ (inj₂ p)    (inj₂ _)    = inj₂ p

      ⁻¹ᴾ : {x : G} → Trivᴾ x → Trivᴾ (x ⁻¹)
      ⁻¹ᴾ (inj₁ x≈ε)  = inj₁ (≈trans (⁻¹-cong x≈ε) ε⁻¹≈ε)
      ⁻¹ᴾ (inj₂ p)    = inj₂ p

      normalᴾ : IsNormal Trivᴾ
      normalᴾ g (inj₁ x≈ε)  = inj₁ (≈trans (conj-cong g x≈ε) (conj-ε g))
      normalᴾ g (inj₂ p)    = inj₂ p

    Trivᴾ-isNormalSubgroup : IsNormalSubgroup Trivᴾ
    Trivᴾ-isNormalSubgroup = record
      { isSubgroup  = mkIsSubgroup 𝒢 respᴾ ∙ᴾ (inj₁ ≈refl) ⁻¹ᴾ
      ; isNormal    = normalᴾ }
```

Now the no-go.  Let `M`{.AgdaBound} be minimal in the unrestricted sense, with a
witness `x₀`{.AgdaBound}.  The normal subgroup `M ∩ Trivᴾ`{.AgdaFunction} is inside
`M`{.AgdaBound}, and it is nontrivial in the negative sense as soon as
`P`{.AgdaBound} is not refutable — so minimality puts `M`{.AgdaBound} inside it, and
reading the second component at `x₀`{.AgdaBound} returns `P`{.AgdaBound}, since
`x₀`{.AgdaBound} is not the identity.

```agda
  -- Unrestricted minimality decides ¬ ¬ P → P for every proposition at the level L.
  minimal→DNE : {M : Pred G L} → IsMinimalNormal M → Witnessed M
    →  (P : Type L) → ¬ ¬ P → P
  minimal→DNE {M} M-min (x₀ , x₀∈M , x₀≉ε) P ¬¬p = read (proj₂ (M⊆N x₀∈M))
    where
    open Oracle P

    N-nsg : IsNormalSubgroup (M ∩ Trivᴾ)
    N-nsg = ∩-isNormalSubgroup (M-min .normalSubgroup) Trivᴾ-isNormalSubgroup

    -- The oracle subgroup meets M nontrivially unless P is refutable.
    N-nontriv : Nontrivial (M ∩ Trivᴾ)
    N-nontriv N⊆Triv = ¬¬p (λ p → x₀≉ε (N⊆Triv (x₀∈M , inj₂ p)))

    M⊆N : M ⊆ (M ∩ Trivᴾ)
    M⊆N = M-min .minimal (M ∩ Trivᴾ) N-nsg (λ z → proj₁ z) N-nontriv

    read : Trivᴾ x₀ → P
    read (inj₁ x₀≈ε)  = ⊥-elim (x₀≉ε x₀≈ε)
    read (inj₂ p)     = p

  -- The Layer-D sharpening: it is the *quantifier* that is classical, not the
  -- presentation.  Even a decidably presented subgroup, minimal in the unrestricted
  -- sense, decides every proposition.
  minimalᵈ→DNE : (𝑴 : Normalᵈ) → IsMinimalNormal (setᵈ 𝑴) → (P : Type L) → ¬ ¬ P → P
  minimalᵈ→DNE 𝑴 M-min = minimal→DNE M-min (witness 𝑴 (M-min .nontrivial))
```

The same argument, with no minimality anywhere, prices the one principle that separates
`IsMinimalNormalʷ`{.AgdaRecord} from `IsMinimalNormal`{.AgdaRecord}: witnessing
nontriviality for arbitrary normal subgroups is itself double-negation elimination.  So
`minimal-normal-descent`{.AgdaFunction} below is not hiding a second classical step
behind the first — there is exactly one, and this is it.

```agda
  -- Witnessing nontriviality unrestrictedly is double-negation elimination.
  witnessing→DNE : WitnessedNontriviality → (𝑴 : Normalᵈ) → Nontrivial (setᵈ 𝑴)
    →  (P : Type L) → ¬ ¬ P → P
  witnessing→DNE wit 𝑴 nontriv P ¬¬p = from-witness (witness 𝑴 nontriv)
    where
    open Oracle P

    M : Pred G L
    M = setᵈ 𝑴

    N-nsg : IsNormalSubgroup (M ∩ Trivᴾ)
    N-nsg = ∩-isNormalSubgroup (isNormalᵈ 𝑴) Trivᴾ-isNormalSubgroup

    -- The oracle subgroup's own witness is not the identity, so its oracle
    -- component cannot be the trivial branch, and P is read off directly.
    read : Witnessed (M ∩ Trivᴾ) → P
    read (_ , (_ , inj₁ y≈ε)  , y≉ε)  = ⊥-elim (y≉ε y≈ε)
    read (_ , (_ , inj₂ p)    , _)    = p

    -- The oracle subgroup is nontrivial unless P is refutable, so the witnessing
    -- principle applies to it.
    from-witness : Witnessed M → P
    from-witness (x₀ , x₀∈M , x₀≉ε) = read (wit (M ∩ Trivᴾ) N-nsg N-nontriv)
      where
      N-nontriv : Nontrivial (M ∩ Trivᴾ)
      N-nontriv N⊆Triv = ¬¬p (λ p → x₀≉ε (N⊆Triv (x₀∈M , inj₂ p)))
```

#### The unrestricted descent, modulo the one principle

Granted `WitnessedNontriviality`{.AgdaFunction} — and by the no-go above nothing
weaker will do — the descent lands in the form [FLRP.Reductions][] threads.

```agda
  -- Minimal-normal descent in the unrestricted form, modulo the witnessing principle.
  minimal-normal-descent : WitnessedNontriviality
    →  (𝑴 : Normalᵈ) → Nontrivial (setᵈ 𝑴)
    →  Σ[ 𝑵 ∈ Normalᵈ ] (IsMinimalNormal (setᵈ 𝑵) × setᵈ 𝑵 ⊆ setᵈ 𝑴)
  minimal-normal-descent wit 𝑴 nontriv =
       proj₁ descended
    ,  minimalʷ→minimal wit (proj₁ (proj₂ descended))
    ,  proj₂ (proj₂ descended)
    where
    descended = minimal-normal-descentᵈ 𝑴 nontriv
```

That still asks its input to be decidably presented, so it is not yet the property
`MinimalNormalDescent`{.AgdaFunction} of [FLRP.Reductions][], which quantifies over
*semantic* normal subgroups.  The gap is one hypothesis, and it is not a new one: it is
the group-side reading of `complete`{.AgdaField} of
`FiniteCongruences`{.AgdaRecord} ([Setoid.Congruences.Finite.Basic][]) — every normal
subgroup is `⊆`-equal to a decidably presented one — which the two-layer note already
identifies as the library's single Layer-S bridge, of strength between weak excluded
middle and excluded middle.

```agda
  -- Every normal subgroup has a decidable presentation: the group-side reading of
  -- `FiniteCongruences.complete`, and the library's Layer-S bridge.
  DecidablyPresented : Type (α ⊔ ρ ⊔ lsuc L)
  DecidablyPresented = (N : Pred G L) → IsNormalSubgroup N
    →  Σ[ 𝑵 ∈ Normalᵈ ] (setᵈ 𝑵 ⊆ N × N ⊆ setᵈ 𝑵)
```

It subsumes the witnessing principle: a nontrivial subgroup's decidable presentation is
nontrivial, hence witnessed by the finite search, and the witness travels back.

```agda
  presented→witnessing : DecidablyPresented → WitnessedNontriviality
  presented→witnessing pres N N-nsg nontriv =
    proj₁ w , proj₁ (proj₂ presentation) (proj₁ (proj₂ w)) , proj₂ (proj₂ w)
    where
    presentation = pres N N-nsg

    -- The presentation is nontrivial, since N is inside it.
    nontrivᵈ : Nontrivial (setᵈ (proj₁ presentation))
    nontrivᵈ ⊆Triv = nontriv (λ z → ⊆Triv (proj₂ (proj₂ presentation) z))

    w : Witnessed (setᵈ (proj₁ presentation))
    w = witness (proj₁ presentation) nontrivᵈ
```

And with it the descent is the property the catalog threads, verbatim.

```agda
  -- Minimal-normal descent, semantic form: every nontrivial normal subgroup of a
  -- finite group with decidably presented normal subgroups contains a minimal one.
  minimal-normal-descent-sem : DecidablyPresented
    →  (N : Pred G L) → IsNormalSubgroup N → Nontrivial N
    →  Σ[ M ∈ Pred G L ] (IsMinimalNormal M × M ⊆ N)
  minimal-normal-descent-sem pres N N-nsg nontriv =
       setᵈ (proj₁ descended)
    ,  proj₁ (proj₂ descended)
    ,  (λ z → proj₁ (proj₂ presentation) (proj₂ (proj₂ descended) z))
    where
    presentation = pres N N-nsg

    nontrivᵈ : Nontrivial (setᵈ (proj₁ presentation))
    nontrivᵈ ⊆Triv = nontriv (λ z → ⊆Triv (proj₂ (proj₂ presentation) z))

    descended = minimal-normal-descent  (presented→witnessing pres)
                                        (proj₁ presentation) nontrivᵈ
```

--------------------------------------
