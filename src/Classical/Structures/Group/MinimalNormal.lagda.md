---
layout: default
file: "src/Classical/Structures/Group/MinimalNormal.lagda.md"
title: "Classical.Structures.Group.MinimalNormal module"
date: "2026-07-26"
author: "the agda-algebras development team"
---

### Minimal normal subgroups and monoliths

This is the [Classical.Structures.Group.MinimalNormal][] module of the [Agda Universal Algebra Library][].

A **minimal normal subgroup** of `G` is a nontrivial normal subgroup that contains no
smaller one, and a **monolith** is a minimal normal subgroup contained in *every*
nontrivial normal subgroup.  A group has a monolith exactly when it is subdirectly
irreducible: for groups, subdirect irreducibility is equivalent to having a unique
minimal normal subgroup.[^1]

The module collects the small facts about these notions that the enforcement catalog
of [FLRP.Reductions][] needs, and nothing else:

+  the notions themselves — `IsNormalSubgroup`{.AgdaRecord},
   `Nontrivial`{.AgdaFunction}, `IsMinimalNormal`{.AgdaRecord},
   `IsMonolithᵍ`{.AgdaRecord}, `HasMonolithᵍ`{.AgdaFunction};
+  `∩-isNormalSubgroup`{.AgdaFunction} — an intersection of normal subgroups is a
   normal subgroup;
+  `minimal-meets→least`{.AgdaFunction} — a minimal normal subgroup that meets every
   nontrivial normal subgroup nontrivially is *contained* in every one of them, hence
   is the monolith.  This is the step that turns the *pairwise* form of subdirect
   irreducibility (the constructive form the parachute theorems of [FLRP.Parachute][]
   prove) into the least-element form the algebra-side
   `IsMonolith`{.AgdaRecord} of [Setoid.Congruences.Monolith][] uses;
+  `abelian→⊆-centralizer`{.AgdaFunction} — an abelian subgroup lies inside its own
   centralizer, so a normal subgroup with trivial centralizer is nonabelian.

Two presentation notes.

+  **The level `L`**.  Subgroup predicates here live at the level `L` of the subgroup
   lattice ([Classical.Structures.Group.SubgroupLattice][]), because the intersection
   fact is the lattice's meet (`∧-isSubgroup`{.AgdaFunction}) rather than a second
   proof of the same closure property.  For a group at levels `α = ρ = 0ℓ` and the
   base level `ℓ₀ = 0ℓ` — the setting the FLRP program fixes — `L` is `0ℓ`.
+  **`ᵍ` marks the group-side form**.  `IsMonolithᵍ`{.AgdaRecord} is the
   normal-subgroup reading of the congruence-lattice notion
   `IsMonolith`{.AgdaRecord}; the two agree through the correspondence between normal
   subgroups and congruences of a group, which the library does not yet formalize.
   The superscript keeps the two apart rather than pretending they are the same
   definition.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.MinimalNormal where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Product     using  ( _×_ ; _,_ ; Σ-syntax ; proj₁ ; proj₂ )
open import Level            using  ( Level ; _⊔_ ) renaming ( suc to lsuc )
open import Relation.Binary  using  ( Setoid )
open import Relation.Nullary using  ( ¬_ )
open import Relation.Unary   using  ( Pred ; _∈_ ; _⊆_ ; _∩_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Group.Basic            using  ( Group ; module Group-Op )
open import Classical.Structures.Group.Centralizer      using  ( module Centralizer )
open import Classical.Structures.Group.Conjugation      using  ( module Conj )
open import Classical.Structures.Group.Subgroups        using  ( IsSubgroup
                                                               ; trivialSubgroup )
open import Classical.Structures.Group.SubgroupLattice  using  ( module GroupSublattice )
open import Setoid.Algebras.Basic                       using  ( 𝕌[_] ; 𝔻[_] )
```
-->

#### Normal subgroups, nontriviality, and trivial meets

Throughout, `𝒢`{.AgdaBound} is a group and `ℓ₀`{.AgdaBound} the base level of its
subgroup lattice; every predicate below lives at the resulting level `L`.

```agda
module MinimalNormal {α ρ : Level} (𝒢 : Group α ρ) (ℓ₀ : Level) where
  private
    𝑮 = proj₁ 𝒢
    G = 𝕌[ 𝑮 ]

  open Setoid 𝔻[ 𝑮 ]  using  ( _≈_ )
  open Group-Op 𝒢     using  ( _∙_ )
  open Centralizer 𝒢  using  ( C[_] )
  open Conj 𝒢         using  ( IsNormal )
  open GroupSublattice 𝒢 ℓ₀  using  ( L ; subgroup→Subᴸ ; ∧-isSubgroup )
```

The trivial subgroup is the `≈`-class of the identity, as elsewhere in the library;
a subgroup is **nontrivial** when it is not contained in it.  (Nontriviality is
stated negatively on purpose: constructively, "not every element is the identity"
carries no witness, and none of the arguments below need one.)

```agda
  -- The trivial subgroup, as a predicate.
  Triv : Pred G ρ
  Triv = proj₁ (trivialSubgroup 𝒢)

  -- N is nontrivial: it is not contained in the trivial subgroup.
  Nontrivial : Pred G L → Type (α ⊔ ρ ⊔ L)
  Nontrivial N = ¬ (N ⊆ Triv)

  -- Two subgroups meet trivially when their intersection is trivial.
  MeetTrivially : Pred G L → Pred G L → Type (α ⊔ ρ ⊔ L)
  MeetTrivially M N = (M ∩ N) ⊆ Triv
```

A **normal subgroup** bundles the two conditions that every statement below
quantifies over together; it is exactly the conjunction of
`IsSubgroup`{.AgdaRecord} and `IsNormal`{.AgdaFunction}, named because it appears in
every hypothesis.

```agda
  record IsNormalSubgroup (N : Pred G L) : Type (α ⊔ ρ ⊔ L) where
    field
      isSubgroup  : IsSubgroup 𝒢 N
      isNormal    : IsNormal N

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
  ∩-isNormalSubgroup M-nsg N-nsg .isNormal g x∈ =
    M-nsg .isNormal g (proj₁ x∈) , N-nsg .isNormal g (proj₂ x∈)
```

#### Minimal normal subgroups

`M` is a **minimal normal subgroup** when it is a nontrivial normal subgroup and
every nontrivial normal subgroup below it is all of it.

```agda
  record IsMinimalNormal (M : Pred G L) : Type (α ⊔ ρ ⊔ lsuc L) where
    field
      normalSubgroup  : IsNormalSubgroup M
      nontrivial      : Nontrivial M
      minimal         : (N : Pred G L) → IsNormalSubgroup N
                      → N ⊆ M → Nontrivial N → M ⊆ N

  open IsMinimalNormal public
```

The key step.  Suppose `M` is a minimal normal subgroup that meets every nontrivial
normal subgroup nontrivially.  Then `M` is *below* every nontrivial normal subgroup
`N`: the intersection `M ∩ N` is a normal subgroup inside `M`, and it is nontrivial
precisely because `M` and `N` do not meet trivially, so minimality gives
`M ⊆ M ∩ N ⊆ N`.

Note that no witness is extracted anywhere: `Nontrivial (M ∩ N)` and
`¬ MeetTrivially M N` are the same statement, so the argument is constructive.

```agda
  minimal-meets→least : (M : Pred G L) → IsMinimalNormal M
    →  ((N : Pred G L) → IsNormalSubgroup N → Nontrivial N → ¬ MeetTrivially M N)
    →  (N : Pred G L) → IsNormalSubgroup N → Nontrivial N → M ⊆ N
  minimal-meets→least M M-min meets N N-nsg N-nontriv z =
    proj₂ (M-min .minimal  (M ∩ N)
                           (∩-isNormalSubgroup (M-min .normalSubgroup) N-nsg)
                           proj₁ (meets N N-nsg N-nontriv) z)
```

#### Monoliths and subdirect irreducibility

A **monolith** is a minimal normal subgroup contained in every nontrivial normal
subgroup.  A group has a monolith exactly when it is subdirectly irreducible;[^1]
`HasMonolithᵍ`{.AgdaFunction} is therefore the group-side statement of subdirect
irreducibility, and `minimal-meets→least`{.AgdaFunction} is how the parachute
theorems of [FLRP.Parachute][] reach it.

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
parachute representation has no nontrivial abelian normal subgroup.[^2]

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
      correspondence between normal subgroups of `G` and congruences of `G`, which is
      not yet formalized (see `docs/notes/flrp-rp2-catalog.md` § 4).

[^2]: `docs/papers/flrp/ieprops/IEProps-1205.1927v4.tex`, the Remark after
      Lemma 3.7: "If `N` is abelian, then `N ≤ C_G(N)`, so (i) implies that every
      nontrivial normal subgroup of `G` is nonabelian."
