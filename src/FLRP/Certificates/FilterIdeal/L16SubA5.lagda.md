---
layout: default
file: "src/FLRP/Certificates/FilterIdeal/L16SubA5.lagda.md"
title: "FLRP.Certificates.FilterIdeal.L16SubA5 module (The Agda Universal Algebra Library)"
date: "2026-08-17"
author: "the agda-algebras development team"
---

### The filter-ideal witness for L16, verified in Sub(A5)

This is the [FLRP.Certificates.FilterIdeal.L16SubA5][] module of the [Agda Universal Algebra Library][].

The census lattice `L16` (seven elements; manuscript numbering) is realized
inside `Sub(A5)` as the union of the filter `[C3 , A5]` and the ideal
`[1 , C5]`: taking `H = C3` of index 20, GAP reports exactly three
intermediate subgroups

```text
[C3 , A5]  =  { C3 , S3 , A4 , A4' , A5 }  ≅  M3
```

(the two `A4`s are the alternating subgroups containing the chosen `C3`, the
`S3` its normalizer), and `K = C5` lies in none of the three middles, meets
each trivially, and joins each to `A5`.  The ambient set has size **60**,
against the 180 of the printed entry (candidate erratum E2 of
`docs/notes/flrp-slr-census.md`).

This module builds that configuration and **re-verifies every part of it by
decision**, in the witness-not-decision style of the WP-6 checkers.  Nothing
below is believed on the engine's authority: a wrong table, subgroup, or word
would make a decidable check compute to `no`{.AgdaInductiveConstructor} and
break compilation.  Specifically it establishes, by computation during
type-checking:

+  the concrete `A5` (carrier `Fin 60`, tables from
   [FLRP.Certificates.FilterIdeal.A5Data][]) is a group, with associativity
   obtained through the faithful permutation action
   ([Classical.Structures.Group.TableGroup][]) rather than the 216 000-case
   cubic sweep;
+  the seven characteristic vectors really do cut out subgroups
   `1 , C3 , C5 , S3 , A4 , A4' , A5`;
+  the emitted **escalation certificates** for both interval families,
   `[C3 , A5]` (five members) and `[1 , C5]` (two members), are
   well-formed, so an arbitrary decidable subgroup in either interval is
   provably one of the listed members
   ([Classical.Structures.Group.SubgroupClassification][]);
+  the seven-element Cayley tables of `L16` satisfy the lattice laws;
+  **order agreement** (`ord-table`{.AgdaFunction}): containment among the
   seven subgroups matches the meet order of those tables, in both
   directions.

Together with Snow's filter-ideal lemma ([FLRP.Closure.FilterIdeal][]) and
the ambient-closedness fact `Sub(A5) = Con (A5 ↷ A5)`
([Classical.Structures.Group.RegularAction][], the WP-3 bridge at `H = 1`,
which is why no unary-reduction theorem[^1] is consumed), these are the
ingredients of an unconditional `Representableᵈ`{.AgdaRecord} witness for
`L16`: one needing neither a postulate nor the Kurzweil–Netter duality
assumption (Entry 2 of [FLRP.Assumptions][]) that the duality route[^2] would
have required.

#### What is not here yet, and why

The final gluing step, feeding this family to
`FilterIdealClosure.Assembly`{.AgdaModule} to obtain the
`Representableᵈ`{.AgdaRecord} value, is **not** in this module.  It is
blocked on an Agda elaboration blowup, not on missing mathematics, and the
diagnosis is worth recording because it shapes any retry (see
`docs/notes/flrp-530-filter-ideal.md` § 4 for the full measurements).

The assembly needs lemmas about the coset congruences of *named* subgroups,
`cosetCon-reflect (proj₁ (S k)) (proj₁ (S l))` for instance.  Elaborating one
such application at this carrier size exhausts a 32 GB heap, while the same
lemma applied to abstract subgroups, and every decision in this module, costs
seconds.  The cost is not in any decision procedure: `ord-table`{.AgdaFunction}
below settles all 49 subgroup containments in about three seconds.  Sealing
the group laws, the subgroup axioms, the congruence proofs, and the round
trips behind `opaque`{.AgdaKeyword} (which is why they are sealed; see
[Classical.Structures.Group.RegularAction][]) removed several layers of the
blowup but not the last one.

The measurements do rule several things out, which is the useful part:
`abstract`{.AgdaKeyword} is *not* a fix inside the defining module, since
its definitions stay transparent there; a `with`-abstraction over a goal
mentioning the family is a separate, additive cost; and forcing a
`from-yes`{.AgdaFunction} payload is far more expensive than merely checking
that the decision says `yes`{.AgdaInductiveConstructor}, so a decision that
is cheap to *state* can be ruinous to *apply*.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.Certificates.FilterIdeal.L16SubA5 where


-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base         using ( Fin )
open import Data.Fin.Patterns     using ( 0F ; 1F ; 2F ; 3F ; 4F ; 5F ; 6F )
open import Data.Fin.Properties   renaming ( all? to allᶠ? ; _≟_ to _≟ᶠ_ ) using ()
open import Data.Product          using ( _×_ )
open import Data.Vec.Base         using ( Vec ; lookup ; _∷_ ; [] )
open import Level                 using ( 0ℓ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ )
open import Relation.Nullary.Decidable.Core        using ( _×-dec_ ; _→-dec_ )
open import Relation.Unary                         using ( _⊆_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Group.RegularAction
                                          using  ( module Regular )
open import Classical.Structures.Group.SubgroupClassification
                                          using  ( module Classify )
open import Classical.Structures.Group.Subgroups
                                          using  ( DecSubgroup )
open import Classical.Structures.Group.TableGroup
                                          using  ( _⨁_ ; module TableGroupBuilder )
open import FLRP.Certificates.FilterIdeal.A5Data
     using  ( permVecs ; mulVecs ; invVec
            ; chi1 ; chiC3 ; chiC5 ; chiS3 ; chiA4 ; chiA4' ; chiA5
            ; filterGens ; filterRank ; filterStepNext ; filterStepWords ; filterExpWords
            ; idealGens ; idealRank ; idealStepNext ; idealStepWords ; idealExpWords )
open import FLRP.Problem                  using  ( FiniteLattice )
open import Overture.Cayley               using  ( Table ; ⟦_⟧ ; from-yes )
open import Overture.Operations.Properties
     using  ( Associative? ; Commutative? ; Idempotent? ; Absorbsˡ? ; Absorbsʳ?
            ; LeftIdentity? ; RightIdentity? ; LeftInverse? ; RightInverse? )
open import Setoid.Congruences.Finite.Basic  using  ( DecCon )
```
-->

#### The group A5

The tables of [FLRP.Certificates.FilterIdeal.A5Data][], read as functions;
the two quadratic action checks and the four linear laws are discharged by
decision, and associativity comes through the faithful action.

The six law witnesses are `opaque`{.AgdaKeyword}, and this is load-bearing
rather than stylistic.  Each is a `from-yes`{.AgdaFunction} of a sweep over
the 60-element carrier (3600 cases for the two action checks), and each ends
up inside the group bundle that every downstream type mentions.  Left
transparent, the proof terms normalize whenever a goal about a *concrete*
subgroup or congruence is checked, and the check exhausts a 6 GB heap;
`opaque`{.AgdaKeyword} stops the unfolding at the name, which costs nothing
because no consumer needs a group law to *compute*, only to exist.

```agda
private
  elt : Fin 60 → Vec (Fin 5) 5
  elt i = lookup permVecs i

  mul : Fin 60 → Fin 60 → Fin 60
  mul i j = lookup (lookup mulVecs i) j

  inv : Fin 60 → Fin 60
  inv i = lookup invVec i

open TableGroupBuilder 60 5 elt mul inv 0F using ( elt-inj? ; mul-hom? )

private
  opaque
    A5-inj : ∀ i j → elt i ≡ elt j → i ≡ j
    A5-inj = from-yes elt-inj?

    A5-hom : ∀ i j → elt (mul i j) ≡ elt i ⨁ elt j
    A5-hom = from-yes mul-hom?

    A5-idˡ : ∀ a → mul 0F a ≡ a
    A5-idˡ = from-yes (LeftIdentity? mul 0F)

    A5-idʳ : ∀ a → mul a 0F ≡ a
    A5-idʳ = from-yes (RightIdentity? mul 0F)

    A5-invˡ : ∀ a → mul (inv a) a ≡ 0F
    A5-invˡ = from-yes (LeftInverse? mul 0F inv)

    A5-invʳ : ∀ a → mul a (inv a) ≡ 0F
    A5-invʳ = from-yes (RightInverse? mul 0F inv)

open TableGroupBuilder.Build 60 5 elt mul inv 0F
  A5-inj A5-hom A5-idˡ A5-idʳ A5-invˡ A5-invʳ
  renaming ( theGroup to A5 ; theGroup-FiniteAlgebra to A5-FiniteAlgebra )
```

#### The seven subgroups

The characteristic vectors of `1 , C3 , C5 , S3 , A4 , A4' , A5`, promoted to
decidable subgroups; each closure obligation is a decidable sweep over the
tables.  The numbering matches the census tables of `L16` below: `0 ↦ 1`,
`1 ↦ C3`, `2 ↦ C5`, `3 ↦ S3`, `4 ↦ A4`, `5 ↦ A4'`, `6 ↦ A5`.

```agda
private
  sub1 sub-C3 sub-C5 sub-S3 sub-A4 sub-A4' sub-A5 : DecSubgroup A5 0ℓ
  sub1     = boolSubgroup chi1    (from-yes (chi-∙? chi1))    (from-yes (chi-ε? chi1))    (from-yes (chi-⁻¹? chi1))
  sub-C3   = boolSubgroup chiC3   (from-yes (chi-∙? chiC3))   (from-yes (chi-ε? chiC3))   (from-yes (chi-⁻¹? chiC3))
  sub-C5   = boolSubgroup chiC5   (from-yes (chi-∙? chiC5))   (from-yes (chi-ε? chiC5))   (from-yes (chi-⁻¹? chiC5))
  sub-S3   = boolSubgroup chiS3   (from-yes (chi-∙? chiS3))   (from-yes (chi-ε? chiS3))   (from-yes (chi-⁻¹? chiS3))
  sub-A4   = boolSubgroup chiA4   (from-yes (chi-∙? chiA4))   (from-yes (chi-ε? chiA4))   (from-yes (chi-⁻¹? chiA4))
  sub-A4'  = boolSubgroup chiA4'  (from-yes (chi-∙? chiA4'))  (from-yes (chi-ε? chiA4'))  (from-yes (chi-⁻¹? chiA4'))
  sub-A5   = boolSubgroup chiA5   (from-yes (chi-∙? chiA5))   (from-yes (chi-ε? chiA5))   (from-yes (chi-⁻¹? chiA5))

  S : Fin 7 → DecSubgroup A5 0ℓ
  S 0F = sub1
  S 1F = sub-C3
  S 2F = sub-C5
  S 3F = sub-S3
  S 4F = sub-A4
  S 5F = sub-A4'
  S 6F = sub-A5
```

#### The ambient: the regular action and its congruences

The ambient algebra is the regular action `A5 ↷ A5`; its decidable
congruences are exactly the coset partitions of decidable subgroups
([Classical.Structures.Group.RegularAction][]).

```agda
open Regular A5 using  ( cosetAlgebra ; regular-FiniteAlgebra ; cosetConᵈ )

private
  𝑭 = regular-FiniteAlgebra A5-FiniteAlgebra

  -- The concrete congruence family carrying L16.
  γ : Fin 7 → DecCon cosetAlgebra 0ℓ
  γ k = cosetConᵈ (S k)
```

#### The two interval classifications

The escalation certificates of the data module, re-verified by decision:
walking an arbitrary decidable subgroup up `[C3 , A5]` (five members, three
middles) and up `[1 , C5]` (two members).

```agda
private
  module C = Classify {ℓ = 0ℓ} A5 A5-FiniteAlgebra

  -- The filter family C3 , S3 , A4 , A4' , A5 inside all of A5.
  fembed : Fin 5 → Fin 7
  fembed 0F = 1F
  fembed 1F = 3F
  fembed 2F = 4F
  fembed 3F = 5F
  fembed 4F = 6F

  module FEsc = C.Escalate sub-A5 (λ k → S (fembed k))
    (λ k → lookup filterGens k)
    (λ k i → lookup (lookup filterExpWords k) i)
    (λ k → lookup filterRank k)
    (λ k j → lookup (lookup filterStepNext k) j)
    (λ k j → lookup (lookup filterStepWords k) j)

  opaque
    fOK : FEsc.EscalationOK
    fOK = from-yes FEsc.escalationOK?

  -- The ideal family 1 , C5 inside C5.
  iembed : Fin 2 → Fin 7
  iembed 0F = 0F
  iembed 1F = 2F

  module IEsc = C.Escalate sub-C5 (λ k → S (iembed k))
    (λ k → lookup idealGens k)
    (λ k i → lookup (lookup idealExpWords k) i)
    (λ k → lookup idealRank k)
    (λ k j → lookup (lookup idealStepNext k) j)
    (λ k j → lookup (lookup idealStepWords k) j)

  opaque
    iOK : IEsc.EscalationOK
    iOK = from-yes IEsc.escalationOK?
```

#### The target lattice

`L16`, presented exactly as `scripts/python/flrp/inputs/slr/slr16_lattice.json`
records it (and as the emitted certificate modules present their targets);
the generator re-derives both tables from the subgroup order and asserts the
match.

```agda
∧-table ∨-table : Table 7
∧-table = (0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ [])
        ∷ (0F ∷ 1F ∷ 0F ∷ 1F ∷ 1F ∷ 1F ∷ 1F ∷ [])
        ∷ (0F ∷ 0F ∷ 2F ∷ 0F ∷ 0F ∷ 0F ∷ 2F ∷ [])
        ∷ (0F ∷ 1F ∷ 0F ∷ 3F ∷ 1F ∷ 1F ∷ 3F ∷ [])
        ∷ (0F ∷ 1F ∷ 0F ∷ 1F ∷ 4F ∷ 1F ∷ 4F ∷ [])
        ∷ (0F ∷ 1F ∷ 0F ∷ 1F ∷ 1F ∷ 5F ∷ 5F ∷ [])
        ∷ (0F ∷ 1F ∷ 2F ∷ 3F ∷ 4F ∷ 5F ∷ 6F ∷ [])
        ∷ []

∨-table = (0F ∷ 1F ∷ 2F ∷ 3F ∷ 4F ∷ 5F ∷ 6F ∷ [])
        ∷ (1F ∷ 1F ∷ 6F ∷ 3F ∷ 4F ∷ 5F ∷ 6F ∷ [])
        ∷ (2F ∷ 6F ∷ 2F ∷ 6F ∷ 6F ∷ 6F ∷ 6F ∷ [])
        ∷ (3F ∷ 3F ∷ 6F ∷ 3F ∷ 6F ∷ 6F ∷ 6F ∷ [])
        ∷ (4F ∷ 4F ∷ 6F ∷ 6F ∷ 4F ∷ 6F ∷ 6F ∷ [])
        ∷ (5F ∷ 5F ∷ 6F ∷ 6F ∷ 6F ∷ 5F ∷ 6F ∷ [])
        ∷ (6F ∷ 6F ∷ 6F ∷ 6F ∷ 6F ∷ 6F ∷ 6F ∷ [])
        ∷ []

open FiniteLattice

𝑳 : FiniteLattice
𝑳 .size     = 6
𝑳 ._∧_      = ⟦ ∧-table ⟧
𝑳 ._∨_      = ⟦ ∨-table ⟧
𝑳 .∧-assoc  = from-yes (Associative? ⟦ ∧-table ⟧)
𝑳 .∧-comm   = from-yes (Commutative? ⟦ ∧-table ⟧)
𝑳 .∧-idem   = from-yes (Idempotent? ⟦ ∧-table ⟧)
𝑳 .∨-assoc  = from-yes (Associative? ⟦ ∨-table ⟧)
𝑳 .∨-comm   = from-yes (Commutative? ⟦ ∨-table ⟧)
𝑳 .∨-idem   = from-yes (Idempotent? ⟦ ∨-table ⟧)
𝑳 .absorbˡ  = from-yes (Absorbsˡ? ⟦ ∧-table ⟧ ⟦ ∨-table ⟧)
𝑳 .absorbʳ  = from-yes (Absorbsʳ? ⟦ ∧-table ⟧ ⟦ ∨-table ⟧)
```

#### Order agreement

The subgroup order of the family reproduces the meet order of the tables:
one decidable statement, both directions at once.

Every decision below is `opaque`{.AgdaKeyword}, and the reason is the same
one that governs this whole module.  Checking a `from-yes`{.AgdaFunction}
*definition* costs only what it takes to see that the decision says
`yes`{.AgdaInductiveConstructor}; **applying** the result forces the proof
term itself, and these proof terms reach the subgroup axioms and thence the
group bundle, whose own law witnesses are decision sweeps over the
60-element carrier.  Measured on this instance, a single such application
exhausts a 32 GB heap.  Sealing each decision behind
`opaque`{.AgdaKeyword} stops the unfolding at the name and costs nothing:
these are proofs of decidable facts, and no consumer needs one to *compute*,
only to exist.

```agda
private
  opaque
    ord-table :  ∀ k l
      →          ((C.set (S k) ⊆ C.set (S l)) → ⟦ ∧-table ⟧ k l ≡ k)
      ×          ((⟦ ∧-table ⟧ k l ≡ k) → (C.set (S k) ⊆ C.set (S l)))
    ord-table = from-yes (allᶠ? (λ k → allᶠ? (λ l →
          (C.sub⊆-dec (S k) (S l) →-dec (⟦ ∧-table ⟧ k l ≟ᶠ k))
      ×-dec ((⟦ ∧-table ⟧ k l ≟ᶠ k) →-dec C.sub⊆-dec (S k) (S l)))))
```


The two directions of `ord-table`{.AgdaFunction} are the substantive
group-theoretic content of the `L16` witness: they say that the seven
subgroups, ordered by inclusion in `Sub(A5)`, *are* the lattice whose Cayley
tables the census records: the filter `[C3 , A5] ≅ M3` sitting above the
ideal `[1 , C5]`.  What remains for the `Representableᵈ`{.AgdaRecord} value
is the mechanical assembly described above.

--------------------------------------

[^1]: The unary-reduction theorem is Issue #501.

[^2]: The duality route for this entry is Issue #529.
