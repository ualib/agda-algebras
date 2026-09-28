---
layout: default
file: "src/FLRP/Reductions/Coatomistic.lagda.md"
title: "FLRP.Reductions.Coatomistic module (The Agda Universal Algebra Library)"
date: "2026-09-28"
author: "the agda-algebras development team"
---

### Entry 13: the parachute analog of Aschbacher's Theorem 3

This is the [FLRP.Reductions.Coatomistic][] module of the [Agda Universal Algebra Library][].

Aschbacher's Theorem 3 (2008)[^1] describes the minimal group representations
of his CD-lattices: if `(H , G)` realizes such a lattice, or its dual, as
`O_G(H) = [H , G]` with `|G|` least, then `G` is almost simple, or `H` is a
complement to `F*(G)` and the interval is a *signalizer lattice*.  The
enforcement catalog's Entry 10 records that every parachute with two big
canopies is one of his D-lattices, so his Proposition 2 applies to it, and
its survey note records that no such parachute is a CD-lattice, because a
canopy has a least element and so the parachute is never atomistic.  The
survey's first reading of Section 6 concluded that both steps of the proof
of Theorem 3 that use the condition (C) therefore fail for parachutes.  That
reading was wrong about the second step, and this module records the
corrected reading as a catalog entry.

**What the two C-dependent steps need**.  Condition (C) is the *coatomistic*
half of "CD": every proper element is a meet of coatoms (his `C*`-lattices;
`IsCoatomistic`{.AgdaFunction} of
[Classical.Structures.Lattice.Disconnected][]).  The atomistic half is never
used in the proof of Theorem 3; it enters only because his minimality ranges
over a lattice *and its dual*, and the class of CD-lattices is closed under
duality.  The two steps are as follows.

+  (6.5): if every maximal overgroup of `H` is of *product type* (his type I,
   `M ∩ D = ∏ M_X`), then `O_G(H)` is isomorphic to `O_Ḡ(H̄)` for the almost
   simple group `Ḡ = Aut_G(L)` of one component `L`, a group of smaller order.
   The isomorphism is his (4.12)(7), and it needs exactly that `O_G(H)` is
   coatomistic: the map `η` from `O_Ḡ(H̄)` hits every maximal overgroup and
   preserves intersections, so it hits every meet of maximal overgroups.
+  (6.6)(3): if maximal overgroups of both types occur, then `L̄_H = 1` and
   `M^III(H) = ∅`.  The proof takes a coatom `M₂` of the component `O₂` and a
   second coatom `M′` of the *same* component with `M₂ ∩ M′ ≠ H`, and the
   condition (C) supplies `M′` because the edge `K < M₂` of `O₂` makes `K` a
   meet of at least two coatoms.  The survey note read this step as needing
   `M₂ ∩ M′ = H`, which two coatoms of one canopy indeed never satisfy; the
   published text (J. Amer. Math. Soc. 21, p. 825) has `M₂ ∩ M′ ≠ H`, and
   two coatoms of one canopy *always* satisfy that, since they meet above the
   canopy's atom (`same-canopy-meet-≢⊥`{.AgdaFunction} of
   [Classical.Structures.Lattice.Disconnected][]).  The extracted text of the
   paper had dropped the symbol `≠`; the page image was read to settle it.

So for a parachute the second step needs only that some canopy on the side
`O₂` has two coatoms, and the first step needs the parachute to be
coatomistic.  Both hold for every coatomistic parachute with two big
canopies: a big coatomistic canopy has at least two coatoms, since its atom
is a meet of that canopy's coatoms and is not itself a coatom.  The proof of
Theorem 3 then goes through *verbatim*, with one exception, discussed next.

**The dual, and the statement imported here**.  Aschbacher's `G*(Λ)` ranges
over representations of `Λ` and of its dual, and his (6.7) uses that: in the
case where every maximal overgroup is of diagonal type and `H ∩ D ≠ 1`, his
(4.13)(4) shows `O_G(H)` is anti-isomorphic to an interval `[N_H* , H₀*]` of
the permutation group `H* ≤ Sym(𝓛)`, so the *dual* of `Λ` is an interval in a
group of smaller order, which contradicts dual-closed minimality.  For a
parachute this is a genuine third alternative, and the dual of a parachute is
not coatomistic, so the analysis cannot be rerun on the dual side.  The entry
therefore states the theorem for representations of the parachute itself and
keeps all four alternatives explicit, over any finite core-free
representation, with the minimality corollaries derived: for `(H , G)`
realizing a coatomistic parachute `Λ` with two big canopies, and `M` the
monolith of `G` (Entry 1 of [FLRP.Reductions][] supplies it),

1.  `M` is simple, so `G` is almost simple (Lemma 3.7 of the note gives
    `C_G(M) = 1`); or
2.  `H` is a complement to `M` (his (6.7)(4)); or
3.  `Λ` is an interval in a group of smaller order (his (6.5), the group
    `Aut_G(L)`); or
4.  the dual of `Λ` is an interval in a group of smaller order (his (6.7),
    the case `D̄_H = L̄`).

Alternative 2 comes with more than the entry states: `H` is transitive on the
components of `M`, induces every inner automorphism of a component
(`L̄_H = L̄`, his (6.7)(3)), and `O_G(H)` is the signalizer lattice `Λ(τ)` of
`τ = (H , N_H(L) , C_H(L))`, his (6.7)(7).  Those clauses need the component
decomposition of a minimal normal subgroup, which the library does not have,
and are recorded in the survey note rather than approximated here.

**What is derived, what is imported**.  The lattice-side vocabulary is
derived: coatoms, the condition (C), and the same-canopy meet lemma that
replaces the note's misreading.  The theorem itself is imported as the named
hypothesis `ParachuteTheorem3`{.AgdaFunction}; its proof is Aschbacher's
Section 6 with the two substitutions above, and it uses the classification of
finite simple groups through his (5.3).  The two corollaries are derived: over
a representation minimal among those of the parachute and its dual
(`DualMinimal`{.AgdaFunction}, his `G*(Λ)`), only alternatives 1 and 2
remain, which is Theorem 3's conclusion; over a representation minimal among
those of the parachute alone, alternative 4 remains as well.

**Where it stands in the program**.  The reduction says what a minimal
representation of a coatomistic parachute looks like, and it imports the
almost simple machinery for such parachutes, but it does not by itself
supply a separating invariant for the RP-3 hunt: the conclusion is a
statement about the pair `(H , G)`, not a group property, and every
alternative is realized by known constructions (alternative 3 by the
wreathed almost simple representations `Ḡ ≀ C₂`, alternative 4 by the double
Kurzweil wreaths, alternative 2 by his Section 8 for canopies with a unique
coatom).  The smallest lattice the entry reaches is `P(2×2 , 2×2)`, the
parachute of two four-element Boolean lattices, eight elements; the
tables-of-marks scan of 2026-09-28 finds it in none of the 414 tables
(`scripts/gap/flrp/out/tomscan_pm2m2.json`), so its representability is
open, and with it the entry's vacuity datum.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.Reductions.Coatomistic where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using  ( ⊥-elim )
open import Data.Nat.Base                          using  ( ℕ ; suc )
                                                   renaming ( _≤_ to _≤ⁿ_ ; _<_ to _<ⁿ_ )
open import Data.Nat.Properties                    using  ( <⇒≱ )
open import Data.Product                           using  ( _×_ ; _,_ ; Σ-syntax ; proj₁ )
open import Data.Sum.Base                          using  ( _⊎_ ; inj₁ ; inj₂ )
open import Level                                  using  ( 0ℓ )
                                                   renaming ( suc to lsuc )
open import Relation.Binary.PropositionalEquality  using  ( _≡_ )
open import Relation.Nullary                       using  ( ¬_ )
open import Relation.Unary                         using  ( Pred ; _∈_ ; _⊆_ ; _∩_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Small.Structures              using  ( Lattice )
open import Classical.Structures.Group              using  ( Group ; IsSubgroup
                                                           ; module Complements
                                                           ; module Conjugate
                                                           ; module MinimalNormal )
open import Classical.Structures.Lattice.Disconnected
                                                    using  ( module ParachuteDisconnected )
open import Classical.Structures.Lattice.Dual       using  ( dualLattice )
open import Classical.Structures.Lattice.Parachute  using  ( Parachute )
open import FLRP.Enforceable                        using  ( CoreFree ; IntervalIso )
open import FLRP.Parachute.Representation           using  ( module ParachuteRep )
open import Setoid.Algebras                         using  ( 𝕌[_] ; FiniteAlgebra )

open FiniteAlgebra using ( card )
```
-->

#### Representations of smaller order

The two "smaller group" alternatives, stated once for an arbitrary lattice:
a representation of `𝑳` over a group whose certified cardinality is smaller
than the given one.  Cardinality is the `card`{.AgdaField} of the
`FiniteAlgebra`{.AgdaRecord} interface, an upper bound on the carrier, as in
`MinimallyIE`{.AgdaFunction} of [FLRP.Reductions][]; with exact enumerations
it is the `|G|` of the literature.

```agda
-- A representation of 𝑳 over a group of smaller certified order than 𝒢.
SmallerRepresentation : (𝒢 : Group 0ℓ 0ℓ) → FiniteAlgebra (proj₁ 𝒢) → Lattice → Type (lsuc 0ℓ)
SmallerRepresentation 𝒢 fin 𝑳 =
  Σ[ 𝒬 ∈ Group 0ℓ 0ℓ ] Σ[ J ∈ Pred 𝕌[ proj₁ 𝒬 ] 0ℓ ] Σ[ J-sg ∈ IsSubgroup 𝒬 J ]
    Σ[ fin′ ∈ FiniteAlgebra (proj₁ 𝒬) ]
      ( fin′ .card <ⁿ fin .card × IntervalIso 𝒬 J J-sg 𝑳 )
```

Aschbacher's minimality: `|G|` is least among all finite representations of
`𝑳` *and of its dual* (his `G*(Λ)`).  The minimality of
`MinimallyIE`{.AgdaFunction}, over representations of `𝑳` alone, is the
weaker `Minimal`{.AgdaFunction}.

```agda
-- 𝒢 is minimal among the finite representations of 𝑳.
Minimal : (𝒢 : Group 0ℓ 0ℓ) → FiniteAlgebra (proj₁ 𝒢) → Lattice → Type (lsuc 0ℓ)
Minimal 𝒢 fin 𝑳 =
  ∀ 𝒬 J J-sg (fin′ : FiniteAlgebra (proj₁ 𝒬)) → IntervalIso 𝒬 J J-sg 𝑳 → fin .card ≤ⁿ fin′ .card

-- 𝒢 is minimal among the finite representations of 𝑳 and of its dual.
DualMinimal : (𝒢 : Group 0ℓ 0ℓ) → FiniteAlgebra (proj₁ 𝒢) → Lattice → Type (lsuc 0ℓ)
DualMinimal 𝒢 fin 𝑳 = Minimal 𝒢 fin 𝑳 × Minimal 𝒢 fin (dualLattice 𝑳)

-- A minimal representation admits no smaller one.
minimal→¬smaller : (𝒢 : Group 0ℓ 0ℓ) (fin : FiniteAlgebra (proj₁ 𝒢)) (𝑳 : Lattice)
  → Minimal 𝒢 fin 𝑳 → ¬ SmallerRepresentation 𝒢 fin 𝑳
minimal→¬smaller 𝒢 fin 𝑳 least (𝒬 , J , J-sg , fin′ , lt , rep) =
  <⇒≱ lt (least 𝒬 J J-sg fin′ rep)
```

#### The lattice-side hypotheses

Fix a parachute with at least two canopies.  The hypotheses of the entry are
the two the proof consumes, both about the parachute lattice: it is
coatomistic (the input of (6.5) through (4.12)(7)), and two of its canopies
have two coatoms each (the input of (6.6)(3), for whichever canopy holds the
product-type maximal overgroups).  The second follows from the first together
with two big canopies, classically; it is kept as a separate hypothesis so
that the entry states exactly what the proof uses, and for a concrete
parachute both are finite computations.

```agda
module CoatomisticParachute {m : ℕ} (𝒫 : Parachute 0ℓ 0ℓ (suc m)) where

  open ParachuteRep 𝒫 public
  open ParachuteDisconnected 𝒫 public using ( IsCoatom ; IsCoatomistic )

  -- Two canopies are big, "|Lᵢ| > 2" twice, as the parachute theorems require.
  TwoBigCanopiesᴸ : Type 0ℓ
  TwoBigCanopiesᴸ = Σ[ p ∈ Ix ] Σ[ q ∈ Ix ] ( ¬ (p ≡ q) × BigCanopyᴸ p × BigCanopyᴸ q )

  -- Canopy i carries two distinct coatoms of the parachute.
  record TwoCoatoms (i : Ix) : Type 0ℓ where
    field
      c₁ c₂      : U i
      c₁-nonTop  : NonTop c₁
      c₂-nonTop  : NonTop c₂
      c₁-coatom  : IsCoatom (can c₁ c₁-nonTop)
      c₂-coatom  : IsCoatom (can c₂ c₂-nonTop)
      distinct   : ¬ (c₁ ≈ c₂)

  -- Two canopies with two coatoms each.
  TwoCoatomCanopies : Type 0ℓ
  TwoCoatomCanopies = Σ[ i ∈ Ix ] Σ[ j ∈ Ix ] ( ¬ (i ≡ j) × TwoCoatoms i × TwoCoatoms j )
```

#### The group-side alternatives

Over a group `𝒢` with a subgroup `H` and a monolith `M` (the least nontrivial
normal subgroup, `HasMonolithᵍ`{.AgdaFunction} of
[Classical.Structures.Group.MinimalNormal][]), the first two alternatives.
A monolith that is simple *as a group* makes `G` almost simple: it is the
unique minimal normal subgroup, and in a parachute representation its
centralizer is trivial (Lemma 3.7).  Simplicity is stated in the implication
form of `IsSimple`{.AgdaFunction} of [Classical.Structures.Group.Simple][],
relativized to `M`: a subgroup of `M` that `M` normalizes and that has a
non-identity member is all of `M`.

```agda
module Alternatives (𝒢@(𝑮 , _) : Group 0ℓ 0ℓ) (H : Pred 𝕌[ 𝑮 ] 0ℓ) where

  open MinimalNormal 𝒢 0ℓ  using  ( HasMonolithᵍ ; HasNontrivialWitness ; Triv )
  open Conjugate 𝒢         using  ( conj )
  open Complements 𝒢       using  ( Factors )

  -- The monolith is simple as a group: G is almost simple.
  MonolithSimple : HasMonolithᵍ → Type (lsuc 0ℓ)
  MonolithSimple (M , _) =
    (N : Pred 𝕌[ 𝑮 ] 0ℓ) → IsSubgroup 𝒢 N → N ⊆ M
    → (∀ {a x} → a ∈ M → x ∈ N → conj a x ∈ N) → HasNontrivialWitness N → M ⊆ N

  -- H is a complement to the monolith: they meet trivially and their product is G.
  ComplementsMonolith : HasMonolithᵍ → Type 0ℓ
  ComplementsMonolith (M , _) = ((H ∩ M) ⊆ Triv) × Factors M H
```

#### Entry 13, imported

**Property**.  A statement about the pair `(H , G)`: the four alternatives
above.

**Enforcing lattice**.  Every coatomistic parachute with two big canopies,
two of whose canopies have two coatoms; `P(2×2 , 2×2)` is the least.

**Source**.  Aschbacher [2008], Section 6, read in the published text, with
(6.5) and (6.6)(3) as discussed above; the group-theoretic input is his
Proposition 2, (4.7) through (4.14), (5.3), and (6.7).  The theorem is about
finite groups, so finiteness is an antecedent, as in Entries 10 and 12.

**Level**.  Every core-free finite representation of the parachute; no
minimality is assumed in the statement, minimality being what the corollaries
add.  The core-free hypothesis is his (6.3) made explicit rather than derived
from minimality.

**Representability status**.  Unknown for every instance: no coatomistic
parachute with two big canopies is known to be a group interval, and the
smallest, `P(2×2 , 2×2)`, is absent from the tables of marks.  Until one is
found the entry is potentially vacuous, exactly as Entry 7 was while `L7`
was open, and it is recorded on the same terms.

```agda
-- Entry 13: Aschbacher's Theorem 3 for coatomistic parachutes with two big
-- canopies, over every finite core-free representation of the parachute.
ParachuteTheorem3 : Type (lsuc 0ℓ)
ParachuteTheorem3 =
  ∀ {m : ℕ} (𝒫 : Parachute 0ℓ 0ℓ (suc m))
  → CoatomisticParachute.IsCoatomistic 𝒫
  → CoatomisticParachute.TwoBigCanopiesᴸ 𝒫
  → CoatomisticParachute.TwoCoatomCanopies 𝒫
  → ∀ 𝒢 H H-sg → CoreFree 𝒢 H H-sg → (fin : FiniteAlgebra (proj₁ 𝒢))
  → IntervalIso 𝒢 H H-sg (CoatomisticParachute.⊕ᵖ-Lattice 𝒫)
  → (mono : MinimalNormal.HasMonolithᵍ 𝒢 0ℓ)
  →   Alternatives.MonolithSimple 𝒢 H mono
    ⊎ Alternatives.ComplementsMonolith 𝒢 H mono
    ⊎ SmallerRepresentation 𝒢 fin (CoatomisticParachute.⊕ᵖ-Lattice 𝒫)
    ⊎ SmallerRepresentation 𝒢 fin (dualLattice (CoatomisticParachute.⊕ᵖ-Lattice 𝒫))
```

#### The two minimality corollaries, derived

Over a representation minimal in Aschbacher's sense, the two "smaller group"
alternatives are impossible, and what remains is the conclusion of Theorem 3:
`G` is almost simple, or `H` is a complement to the monolith.  Over a
representation minimal among those of the parachute alone, the dual
alternative survives.  Each case split is a named helper taking the
disjunction as an argument.

```agda
module Corollaries {m : ℕ} (𝒫 : Parachute 0ℓ 0ℓ (suc m))
  (𝒢 : Group 0ℓ 0ℓ) (H : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ) (fin : FiniteAlgebra (proj₁ 𝒢))
  (mono : MinimalNormal.HasMonolithᵍ 𝒢 0ℓ)
  where

  open CoatomisticParachute 𝒫  using  ( ⊕ᵖ-Lattice )
  open Alternatives 𝒢 H        using  ( MonolithSimple ; ComplementsMonolith )

  private
    Λ Λ′ : Lattice
    Λ   = ⊕ᵖ-Lattice
    Λ′  = dualLattice ⊕ᵖ-Lattice

    -- Discard the alternatives a minimality hypothesis refutes.
    dispatch-dual : ¬ SmallerRepresentation 𝒢 fin Λ → ¬ SmallerRepresentation 𝒢 fin Λ′
      →   MonolithSimple mono ⊎ ComplementsMonolith mono
        ⊎ SmallerRepresentation 𝒢 fin Λ ⊎ SmallerRepresentation 𝒢 fin Λ′
      → MonolithSimple mono ⊎ ComplementsMonolith mono
    dispatch-dual _  _  (inj₁ s)               = inj₁ s
    dispatch-dual _  _  (inj₂ (inj₁ c))        = inj₂ c
    dispatch-dual no _  (inj₂ (inj₂ (inj₁ r))) = ⊥-elim (no r)
    dispatch-dual _  no (inj₂ (inj₂ (inj₂ r))) = ⊥-elim (no r)

    dispatch : ¬ SmallerRepresentation 𝒢 fin Λ
      →   MonolithSimple mono ⊎ ComplementsMonolith mono
        ⊎ SmallerRepresentation 𝒢 fin Λ ⊎ SmallerRepresentation 𝒢 fin Λ′
      → MonolithSimple mono ⊎ ComplementsMonolith mono ⊎ SmallerRepresentation 𝒢 fin Λ′
    dispatch _  (inj₁ s)               = inj₁ s
    dispatch _  (inj₂ (inj₁ c))        = inj₂ (inj₁ c)
    dispatch no (inj₂ (inj₂ (inj₁ r))) = ⊥-elim (no r)
    dispatch _  (inj₂ (inj₂ (inj₂ r))) = inj₂ (inj₂ r)

  -- Theorem 3 for parachutes: a dual-minimal representation of a coatomistic
  -- parachute with two big canopies is almost simple or a complement.
  theorem3-dualMinimal : ParachuteTheorem3
    → CoatomisticParachute.IsCoatomistic 𝒫
    → CoatomisticParachute.TwoBigCanopiesᴸ 𝒫
    → CoatomisticParachute.TwoCoatomCanopies 𝒫
    → (H-sg : IsSubgroup 𝒢 H) → CoreFree 𝒢 H H-sg → IntervalIso 𝒢 H H-sg Λ
    → DualMinimal 𝒢 fin Λ
    → MonolithSimple mono ⊎ ComplementsMonolith mono
  theorem3-dualMinimal thm coat big two H-sg cf iso (least , least′) =
    dispatch-dual (minimal→¬smaller 𝒢 fin Λ least) (minimal→¬smaller 𝒢 fin Λ′ least′)
                  (thm 𝒫 coat big two 𝒢 H H-sg cf fin iso mono)

  -- Over minimality among representations of the parachute alone, the dual
  -- alternative remains: this is what Aschbacher's dual-closed minimality buys.
  theorem3-minimal : ParachuteTheorem3
    → CoatomisticParachute.IsCoatomistic 𝒫
    → CoatomisticParachute.TwoBigCanopiesᴸ 𝒫
    → CoatomisticParachute.TwoCoatomCanopies 𝒫
    → (H-sg : IsSubgroup 𝒢 H) → CoreFree 𝒢 H H-sg → IntervalIso 𝒢 H H-sg Λ
    → Minimal 𝒢 fin Λ
    → MonolithSimple mono ⊎ ComplementsMonolith mono ⊎ SmallerRepresentation 𝒢 fin Λ′
  theorem3-minimal thm coat big two H-sg cf iso least =
    dispatch (minimal→¬smaller 𝒢 fin Λ least) (thm 𝒫 coat big two 𝒢 H H-sg cf fin iso mono)
```

---

[^1]: M. Aschbacher, *On intervals in subgroup lattices of finite groups*,
      J. Amer. Math. Soc. 21 (2008), 809–830: Theorem 3 and its proof in
      Section 6, with the reduction machinery of Section 4 and the
      construction of Sections 7 and 8.  The specialization to parachutes,
      the reading of (6.6)(3), and the computational record for
      `P(2×2 , 2×2)` are in `docs/notes/flrp-parachute-theorem3.md`.
