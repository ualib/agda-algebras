---
layout: default
file: "src/Classical/Structures/Group/MinimalNormal.lagda.md"
title: "Classical.Structures.Group.MinimalNormal module"
date: "2026-07-26"
author: "the agda-algebras development team"
---

### Minimal normal subgroups and monoliths

This is the [Classical.Structures.Group.MinimalNormal][] module of the [Agda Universal Algebra Library][].

A **minimal normal subgroup** of `G` is a nontrivial normal subgroup that contains
no smaller one.  A **monolith** is a minimal normal subgroup contained in every
nontrivial normal subgroup.

A group has a monolith exactly when it is subdirectly irreducible: for groups,
subdirect irreducibility is equivalent to having a unique minimal normal
subgroup.[^1]

This module collects the following set of facts about these notions that the
enforcement catalog of [FLRP.Reductions][] needs:

+  the notions themselves: `IsNormalSubgroup`{.AgdaRecord},
   `Nontrivial`{.AgdaFunction}, `IsMinimalNormal`{.AgdaRecord},
   `IsMonolithᵍ`{.AgdaRecord}, `HasMonolithᵍ`{.AgdaFunction};
+  `∩-isNormalSubgroup`{.AgdaFunction}: an intersection of normal subgroups is a
   normal subgroup;
+  `minimal-meets→below`{.AgdaFunction} and `minimal-meets→least`{.AgdaFunction}: a
   minimal normal subgroup is contained in every nontrivial normal subgroup that it
   intersects nontrivially, hence is the monolith when it intersects all of them
   nontrivially;[^2]
+  `abelian→⊆-centralizer`{.AgdaFunction}: an abelian subgroup lies inside its own
   centralizer, so a normal subgroup with trivial centralizer is nonabelian;
+  `HasNontrivialWitness`{.AgdaFunction} and `IsMinimalNormalʷ`{.AgdaRecord}: the *witnessed*
   readings of nontriviality and of minimality, which is what a constructive
   existence proof for minimal normal subgroups can deliver
   ([Classical.Structures.Group.MinimalNormalDescent][]).

**Two presentation notes**.

+  **The level `L`**.  Subgroup predicates here live at the level `L` of the
   subgroup lattice ([Classical.Structures.Group.SubgroupLattice][]), because the
   intersection fact is the lattice's meet (`∧-isSubgroup`{.AgdaFunction}) rather
   than a second proof of the same closure property; for a group at levels
   `α = ρ = 0ℓ` and base level `ℓ₀ = 0ℓ`, `L` is `0ℓ`.
+  **`ᵍ` marks the group-side form**.  `IsMonolithᵍ`{.AgdaRecord} is the
   normal-subgroup reading of the congruence-lattice notion
   `IsMonolith`{.AgdaRecord}; the two agree through the correspondence between
   normal subgroups and congruences of a group.[^3]

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.MinimalNormal where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Product     using  ( _×_ ; _,_ ; Σ-syntax ; proj₁ ; proj₂ ; ∃-syntax )
open import Level            using  ( Level ; _⊔_ ) renaming ( suc to lsuc )
open import Function         using (_∘_)
open import Relation.Binary  using  ( Setoid )
open import Relation.Nullary using  ( ¬_ )
open import Relation.Unary   using  ( Pred ; _∈_ ; _⊆_ ; _∩_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Group.Basic            using  ( Group ; module Group-Op )
open import Classical.Structures.Group.Centralizer      using  ( module Centralizer )
open import Classical.Structures.Group.Conjugation      using  ( module Conjugate )
open import Classical.Structures.Group.Subgroups        using  ( IsSubgroup
                                                               ; trivialSubgroup )
open import Classical.Structures.Group.SubgroupLattice  using  ( module GroupSublattice )
open import Setoid.Algebras.Basic                       using  ( 𝕌[_] ; 𝔻[_] )
```
-->

#### Normal subgroups, nontriviality, and trivial meets

Throughout, `𝒢` is a group and `ℓ₀` the base level of its subgroup lattice; every
predicate below lives at the resulting level `L`.

```agda
module MinimalNormal {α ρ : Level} (𝒢@(𝑮 , _) : Group α ρ) (ℓ₀ : Level) where
  private
    G : Type α
    G = 𝕌[ 𝑮 ]

  open Setoid 𝔻[ 𝑮 ]         using  ( _≈_ )
  open Group-Op 𝒢            using  ( _∙_ ; ε )
  open Centralizer 𝒢         using  ( C[_] )
  open Conjugate 𝒢           using  ( IsNormal )
  open GroupSublattice 𝒢 ℓ₀  using  ( L ; subgroup→Subᴸ ; ∧-isSubgroup )
```

The trivial subgroup is the `≈`-class of the identity, as elsewhere in the
library; a subgroup is **nontrivial** when it is not contained in it.
(Nontriviality is stated negatively on purpose: constructively, "not every element
is the identity" carries no witness, and none of the arguments of this section and
the next need one.  The witnessed reading, which the descent of
[Classical.Structures.Group.MinimalNormalDescent][] does need, is named separately
further below.)

```agda
  -- The trivial subgroup, as a predicate.
  Triv : Pred G ρ
  Triv = trivialSubgroup 𝒢 .proj₁

  -- N is nontrivial: it is not contained in the trivial subgroup.
  Nontrivial : Pred G L → Type (α ⊔ ρ ⊔ L)
  Nontrivial N = ¬ N ⊆ Triv

  -- Two subgroups meet trivially when their intersection is trivial.
  MeetTrivially : Pred G L → Pred G L → Type (α ⊔ ρ ⊔ L)
  MeetTrivially M N = (M ∩ N) ⊆ Triv
```

A **normal subgroup** bundles the two conditions that every statement below
quantifies over; it is exactly the conjunction of `IsSubgroup`{.AgdaRecord} and
`IsNormal`{.AgdaFunction}, named because it appears in every hypothesis.

```agda
  record IsNormalSubgroup (N : Pred G L) : Type (α ⊔ ρ ⊔ L) where
    field
      isSubgroup  : IsSubgroup 𝒢 N    -- closed under ops and respects equality
      isNormal    : IsNormal N        -- closed under conjugation

  open IsNormalSubgroup public
```

An intersection of normal subgroups is a normal subgroup: the subgroup half is the
meet of the subgroup lattice, and the normality half is conjugation acting
componentwise.

```agda
  ∩-isNormalSubgroup : {M N : Pred G L}
    →  IsNormalSubgroup M → IsNormalSubgroup N → IsNormalSubgroup (M ∩ N)
  ∩-isNormalSubgroup {M} {N} M-nsg N-nsg .isSubgroup =
    ∧-isSubgroup  (subgroup→Subᴸ M (M-nsg .isSubgroup))
                  (subgroup→Subᴸ N (N-nsg .isSubgroup))
                  (M-nsg .isSubgroup) (N-nsg .isSubgroup)
  ∩-isNormalSubgroup M-nsg N-nsg .isNormal g (x∈M , x∈N) =
    M-nsg .isNormal g x∈M , N-nsg .isNormal g x∈N
```

#### Minimal normal subgroups

`M` is a **minimal normal subgroup** when it is a nontrivial normal subgroup and
the only nontrivial normal subgroup it contains is itself.

```agda
  record IsMinimalNormal (M : Pred G L) : Type (α ⊔ ρ ⊔ lsuc L) where
    field
      normalSubgroup  : IsNormalSubgroup M
      nontrivial      : Nontrivial M
      minimal         : ∀ N → IsNormalSubgroup N → N ⊆ M → Nontrivial N → M ⊆ N

  open IsMinimalNormal public
```

**The key step**.  Suppose `M` is a minimal normal subgroup and `N` is a
nontrivial normal subgroup that `M` does not meet trivially.  Then `M` is *below*
`N`: the intersection `M ∩ N` is a normal subgroup inside `M`, and it is nontrivial
precisely because `M` and `N` do not meet trivially, so minimality gives
`M ⊆ M ∩ N ⊆ N`.

Note that no witness is extracted anywhere: `Nontrivial (M ∩ N)` and
`¬ MeetTrivially M N` are the same statement, so the argument is constructive.

```agda
  -- A minimal normal subgroup lies below every nontrivial normal subgroup that
  -- it does not meet trivially.
  minimal-meets→below : (M N : Pred G L) → IsMinimalNormal M
    → IsNormalSubgroup N → Nontrivial N → ¬ MeetTrivially M N → M ⊆ N
  minimal-meets→below M N M-min N-nsg N-nontriv MN = proj₂ ∘ M⊆MN
    where
    M⊆MN : M ⊆ (M ∩ N)
    M⊆MN = M-min .minimal (M ∩ N)
      (∩-isNormalSubgroup (M-min .normalSubgroup) N-nsg) proj₁ MN
```

Quantifying over `N` gives the form the monolith record below asks for: a minimal
normal subgroup that meets every nontrivial normal subgroup nontrivially is below
every one of them.

```agda
  -- A minimal normal subgroup that meets every nontrivial normal subgroup
  -- nontrivially is below every one of them.
  minimal-meets→least : (M : Pred G L) → IsMinimalNormal M
    → (  ∀ N → IsNormalSubgroup N → Nontrivial N → ¬ MeetTrivially M N)
    →    ∀ N → IsNormalSubgroup N → Nontrivial N → M ⊆ N
  minimal-meets→least M M-min meets N N-nsg N-nontriv =
    minimal-meets→below M N M-min N-nsg N-nontriv (meets N N-nsg N-nontriv)
```

#### Witnessed nontriviality, and minimality against witnessed subgroups

`Nontrivial`{.AgdaFunction} is stated negatively, and that is the right choice for
the arguments above; but a proof that a minimal normal subgroup exists cannot
consume it.

Over a finite group a witness can be recovered for a normal subgroup whose
membership is decidable, and only for such a subgroup: `witness`{.AgdaFunction} of
[Classical.Structures.Group.MinimalNormalDescent][] does the finite search, and
the no-go theorem of that module shows the unrestricted passage from
`Nontrivial`{.AgdaFunction} to `HasNontrivialWitness`{.AgdaFunction} is equivalent to
double-negation elimination.  So the two readings are named separately here.

```agda
  -- N is nontrivial, witnessed: some member of N is not the identity.
  HasNontrivialWitness : Pred G L → Type (α ⊔ ρ ⊔ L)
  HasNontrivialWitness N = ∃[ y ] (y ∈ N × ¬ y ≈ ε)

  -- A witness refutes containment in the trivial subgroup.
  witnessed→nontrivial : {N : Pred G L} → HasNontrivialWitness N → Nontrivial N
  witnessed→nontrivial (_ , y∈N , y≉ε) N⊆Triv = y≉ε (N⊆Triv y∈N)
```

The matching reading of minimality quantifies over the normal subgroups that come
with a witness.  It is *not* a weakening of `IsMinimalNormal`{.AgdaRecord} in the
domain of quantification; the subgroups it ranges over are arbitrary, with no
decidability assumed.  It is only a change in the form of the nontriviality
hypothesis.

```agda
  record IsMinimalNormalʷ (M : Pred G L) : Type (α ⊔ ρ ⊔ lsuc L) where
    field
      normalSubgroupʷ  : IsNormalSubgroup M
      witnessedʷ       : HasNontrivialWitness M
      minimalʷ         : ∀ N → IsNormalSubgroup N → N ⊆ M → HasNontrivialWitness N → M ⊆ N

  open IsMinimalNormalʷ public
```

The gap between the two records is one named principle, and naming it keeps the
classical content in a single place rather than spread over the consumers.

```agda
  -- Every nontrivial normal subgroup has a witness.
  WitnessedNontriviality : Type (α ⊔ ρ ⊔ lsuc L)
  WitnessedNontriviality =
    (N : Pred G L) → IsNormalSubgroup N → Nontrivial N → HasNontrivialWitness N

  -- Granted that principle, witnessed minimality is minimality.
  minimalʷ→minimal : WitnessedNontriviality → {M : Pred G L}
    →  IsMinimalNormalʷ M → IsMinimalNormal M
  minimalʷ→minimal wit M-min = record
    { normalSubgroup  = M-min .normalSubgroupʷ
    ; nontrivial      = witnessed→nontrivial (M-min .witnessedʷ)
    ; minimal         = λ N N-nsg N⊆M N-nontriv →
                          M-min .minimalʷ N N-nsg N⊆M (wit N N-nsg N-nontriv)
    }
```

#### Monoliths and subdirect irreducibility

A **monolith** is a minimal normal subgroup contained in every nontrivial normal
subgroup.  A group has a monolith exactly when it is subdirectly irreducible.[^1]
`HasMonolithᵍ`{.AgdaFunction} is therefore the group-side statement of subdirect
irreducibility, and `minimal-meets→least`{.AgdaFunction} is how the parachute
theorems of [FLRP.Parachute][] reach this characterization.

```agda
  record IsMonolithᵍ (M : Pred G L) : Type (α ⊔ ρ ⊔ lsuc L) where
    field
      isMinimalNormal  : IsMinimalNormal M
      least            : (N : Pred G L) → IsNormalSubgroup N → Nontrivial N → M ⊆ N

  -- G has a monolith: a least nontrivial normal subgroup.
  HasMonolithᵍ : Type (α ⊔ ρ ⊔ lsuc L)
  HasMonolithᵍ = Σ[ M ∈ Pred G L ] IsMonolithᵍ M
```

The monolith is unique up to mutual containment — two least nontrivial normal
subgroups are each below the other — mirroring
`monolith-unique`{.AgdaFunction} of [Setoid.Congruences.Monolith][].

```agda
  open IsMonolithᵍ public

  monolithᵍ-unique : (m m' : HasMonolithᵍ)
    →  (proj₁ m ⊆ proj₁ m') × (proj₁ m' ⊆ proj₁ m)
  monolithᵍ-unique (μ , mono) (μ' , mono') =
       mono   .least μ' (mono' .isMinimalNormal .normalSubgroup)
                        (mono' .isMinimalNormal .nontrivial)
    ,  mono'  .least μ  (mono  .isMinimalNormal .normalSubgroup)
                        (mono  .isMinimalNormal .nontrivial)
```

#### Abelian subgroups and centralizers

A subgroup is **abelian** when its elements commute with one another; such a subgroup
lies inside its own centralizer, so a subgroup with trivial centralizer is either
trivial or nonabelian.  This is the whole content of the note's remark that a
parachute representation has no nontrivial abelian normal subgroup.[^4]

```agda
  -- N is abelian: its elements commute with each other.
  Abelian : Pred G L → Type (α ⊔ ρ ⊔ L)
  Abelian N = ∀ x y → x ∈ N → y ∈ N → x ∙ y ≈ y ∙ x

  -- An abelian subgroup centralizes itself.
  abelian→⊆-centralizer : {N : Pred G L} → Abelian N → N ⊆ C[ N ]
  abelian→⊆-centralizer ab {x} x∈N y y∈N = ab x y x∈N y∈N

  -- Hence an abelian subgroup whose centralizer is trivial is itself trivial.
  abelian-centralizer-trivial : {N : Pred G L}
    →  Abelian N → C[ N ] ⊆ Triv → N ⊆ Triv
  abelian-centralizer-trivial ab cent z = cent (abelian→⊆-centralizer ab z)
```

---

[^1]: See `docs/papers/flrp/ieprops/IEProps-1205.1927v4.tex`, the footnote to
      § 3: "Recall, for groups *subdirectly irreducible* is equivalent to having a
      unique minimal normal subgroup."  The universal-algebra-side notion is
      `IsSubdirectlyIrreducible`{.AgdaFunction} of [Setoid.Congruences.Monolith][],
      stated for the congruence lattice of an algebra; the two are identified by the
      correspondence between normal subgroups of `G` and congruences of `G` of
      [Classical.Structures.Group.Congruences][] (see footnote 3).

[^2]: This is the step that turns the pairwise form of subdirect irreducibility
      (the constructive form the parachute theorems of [FLRP.Parachute][] prove)
      into the least-element form the algebra-side `IsMonolith`{.AgdaRecord} of
      [Setoid.Congruences.Monolith][] uses.

[^3]: The correspondence between the normal subgroups and the congruences of a
      group is formalized in [Classical.Structures.Group.Congruences][] (M6-22).
      The transport of `HasMonolithᵍ`{.AgdaFunction} across it to the algebra-side
      `HasMonolith`{.AgdaFunction} has not been carried out; until it is, the
      superscript keeps the two notions apart rather than pretending they are the
      same definition.  The simplicity instance of the same identification is
      proved in that module: the group-theoretic notion is equivalent to the
      congruence-level `IsSimple`{.AgdaFunction} of [Setoid.Congruences.Simple][],
      constructively in both directions.

[^4]: `docs/papers/flrp/ieprops/IEProps-1205.1927v4.tex`, the Remark after
      Lemma 3.7: "If `N` is abelian, then `N ≤ C_G(N)`, so (i) implies that every
      nontrivial normal subgroup of `G` is nonabelian."
