---
layout: default
file: "src/Classical/Structures/Group/PowerCollapse.lagda.md"
title: "Classical.Structures.Group.PowerCollapse module"
date: "2026-09-02"
author: "the agda-algebras development team"
---

### Blockwise collapse above the diagonal of a power

This is the [Classical.Structures.Group.PowerCollapse][] module of the [Agda Universal Algebra Library][].

**Theorem (Kurzweil's surjectivity lemma, decidable form).**  Let `S` be a finite nonabelian simple group and `U` a subgroup of the power `Sⁿ` that contains the diagonal and has decidable membership.  Then `U` is a partition subgroup: for the partition `π` computed as the joint kernel of the members of `U`, the subgroup `U` and the partition subgroup `K_π` of [Classical.Structures.Group.PartitionSubgroup][] contain one another.

The classical sources state this for arbitrary subgroups; over arbitrary respecting predicates the statement is *unprovable* in the safe fragment (producing the partition from an oracle subgroup decides an arbitrary proposition, the no-go of the FLRP development), so the decidable-membership hypothesis is load-bearing, not a convenience.  With it, every quantifier the argument opens is a search over a finite enumeration, and the proof is fully constructive.

The proof is the classical one, arranged so that simplicity is applied to subgroups of the *base* group only:

1. **The joint kernel.**  Coordinates `i` and `j` are equivalent when every member of `U` agrees there; the relation is decidable by enumerating the power, and choosing least representatives turns it into a parent vector `π`.  One containment, `U ⊆ K_π`, is the definition unwinding.

2. **Killed projections.**  For a set `T` of coordinates and a coordinate `i`, the values at `i` of members of `U` vanishing on `T` form a subgroup of `S`, normalized by the diagonal conjugation action.  It is the recipient of every simplicity application below.

3. **Separation.**  If `i` and `j` are inequivalent, some member of `U` separates them; renormalizing by a diagonal factor produces a member vanishing at `j` and not at `i`.  Feeding it to the killed projection at `T = {j}`, simplicity makes that projection everything: members of `U` vanishing at `j` realize *every* value at `i`.

4. **Support shrinking.**  Iterating commutators against such members kills the coordinates outside the block of `i` one at a time while the value at `i` stays away from the identity: a commutator vanishes wherever either factor vanishes, and the partner's value at `i` is chosen, by triviality of the center and a finite search, to not commute with the accumulated value.  The result is a member of `U` supported in the block of `i` and nontrivial at `i`.

5. **Columns and the fold.**  Feeding that member to the killed projection at the complement of the block, simplicity realizes every value `s` as a member supported in the block; such a member is *constant* on the block, because the block is a block of the joint kernel, so it is the block column with value `s`, and `K_π ⊆ U` follows by peeling one block column off a `K_π`-member per block representative.

Nonabelianness enters exactly twice, both times through the derived triviality of the center of [Classical.Structures.Group.Simple][]: the seed `s₀` of the iteration is one element of the non-commuting pair, and the finite search for a non-commuting partner needs a centerless base.  Simplicity enters only through steps 3 and 5.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.PowerCollapse where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Bool.Base      using ( if_then_else_ )
open import Data.Empty          using ( ⊥-elim )
open import Data.Fin.Base       using ( Fin ; toℕ ; Fin′ ; inject ; fromℕ< )
open import Data.Fin.Properties using ( any? ; all? ; toℕ-injective ; toℕ-inject
                                      ; toℕ-fromℕ< ; toℕ<n ; ¬∀⟶∃¬ ; ¬∀⟶∃¬-smallest )
                                renaming ( _≟_ to _≟f_ )
open import Data.List.Base      using ( List ; [] ; _∷_ ; filter ; allFin )
open import Data.List.Relation.Unary.Any          using ( here ; there )
open import Data.List.Membership.Propositional    using () renaming ( _∈_ to _∈ˡ_ )
open import Data.List.Membership.Propositional.Properties
                                using ( ∈-allFin ; ∈-filter⁺ ; ∈-filter⁻ )
open import Data.Nat.Base       using ( ℕ ; zero ; suc ; _+_ ; _<_ ; s≤s )
open import Data.Nat.Properties using ( <-cmp ; <-irrefl ; <-asym ; ≤⇒≯ ; ≤-reflexive
                                      ; m<n⇒m<1+n ; +-suc ; +-identityʳ ; _<?_ )
                                renaming ( _≟_ to _≟ℕ_ )
open import Data.Product        using ( Σ-syntax ; ∃ ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Vec.Base       using ( tabulate )
open import Data.Vec.Properties using ( lookup∘tabulate )
open import Level               using ( 0ℓ )
open import Relation.Binary     using ( Setoid )
open import Relation.Binary.Definitions           using ( Tri ; tri< ; tri≈ ; tri> )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; cong ; subst )
                                renaming ( sym to ≡sym ; trans to ≡trans )
open import Relation.Nullary    using ( ¬_ ; Dec ; yes ; no ; ¬? ; decidable-stable )
open import Relation.Nullary.Decidable            using ( does ; dec-true ; dec-false
                                                        ; map′ ; _→-dec_ )
open import Relation.Unary      using ( Pred ; _∈_ ; _⊆_ )

import Algebra.Properties.Group as GroupProperties
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Bundles.Group                      using  ( ⟨_⟩ᵍᵖ )
open import Classical.Structures.Group.Basic             using  ( Group
                                                                ; module Group-Op )
open import Classical.Structures.Group.Commutator        using  ( module Commutator )
open import Classical.Structures.Group.Congruences       using  ( module GroupCongruences )
open import Classical.Structures.Group.MinimalNormal     using  ( module MinimalNormal )
open import Classical.Structures.Group.PartitionSubgroup using  ( module PartitionSubgroups )
open import Classical.Structures.Group.Simple            using  ( module Simple )
open import Classical.Structures.Group.Subgroups         using  ( IsSubgroup
                                                                ; mkIsSubgroup )
open import Classical.Structures.Lattice.Partitions      using  ( SameBlock )
open import Setoid.Algebras.Basic                        using  ( 𝕌[_] ; 𝔻[_] )
open import Setoid.Algebras.Finite                       using  ( FiniteAlgebra )
open import Setoid.Algebras.Products.Finite              using  ( power-FiniteAlgebra )
open import Setoid.Congruences.Certificates.Schema       using  ( ParentVec ; parent )
```
-->

#### The collapse module

`PowerCollapse`{.AgdaModule} fixes the exponent, the base group with its finiteness witness and nonabelian-simplicity bundle, and the subgroup: a respecting subgroup `U` of the power with a membership decider, containing the diagonal.  The four `U`-hypotheses are exactly the unbundled content of a decidable interval element of `[D , Sⁿ]`, stated here without interval vocabulary so that the module stays below the FLRP layer.

```agda
module PowerCollapse
  (n           : ℕ)
  (𝒮@(𝑺 , _)   : Group 0ℓ 0ℓ)
  (𝑭ₛ          : FiniteAlgebra 𝑺)
  (nas         : Simple.IsNonabelianSimple 𝒮 0ℓ)
  (U           : Pred 𝕌[ proj₁ (PartitionSubgroups.⨅ᵍ-Group n 𝒮) ] 0ℓ)
  (U-sg        : IsSubgroup (PartitionSubgroups.⨅ᵍ-Group n 𝒮) U)
  (U-dec       : ∀ x → Dec (x ∈ U))
  (D⊆U         : PartitionSubgroups.Diag n 𝒮 ⊆ U)
  where

  open PartitionSubgroups n 𝒮
  private
    Π𝑮 = ⨅ᵍ-Group .proj₁

  open Setoid 𝔻[ 𝑺 ]   using ( _≈_ ; reflexive )
                       renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open Setoid 𝔻[ Π𝑮 ]  using () renaming ( _≈_ to _≈ᴾ_ ; sym to ≈ᴾ-sym )
  open SetoidReasoning 𝔻[ 𝑺 ]

  open Group-Op 𝒮       using  ( _∙_ ; ε ; _⁻¹ ; ∙-cong ; ⁻¹-cong
                               ; idˡ-law ; idʳ-law ; invʳ-law )
  open Group-Op ⨅ᵍ-Group  using () renaming ( _∙_ to _⊗_ ; ε to εᴾ ; _⁻¹ to invᴾ )
  open GroupProperties ⟨ 𝒮 ⟩ᵍᵖ     using  ( ε⁻¹≈ε )
  open GroupCongruences 𝒮          using  ( ∙⁻¹≈ε→≈ )
  open Commutator 𝒮                using  ( Commutes ; Commutes-congʳ ; comm
                                          ; comm-cong ; comm-εˡ ; comm-εʳ
                                          ; comm≈ε→commutes )
  open Commutator ⨅ᵍ-Group         using () renaming ( comm to commᴾ )
  open Simple 𝒮 0ℓ                 using  ( IsNonabelianSimple ; center
                                          ; center-trivial ; ≈-dec→Stable-≈ε
                                          ; simple ; elt ; elt≉ε )
  open MinimalNormal 𝒮 0ℓ          using  ( IsNormalSubgroup ; isSubgroup ; isNormal )
  open IsSubgroup U-sg             using () renaming ( respects to U-resp
                                                      ; ∙-closed to U-∙
                                                      ; ⁻¹-closed to U-inv )
```

The finiteness witnesses: the base enumeration drives the searches inside the base group, and the power enumeration drives the searches over members of `U`.

```agda
  private
    _≟ₛ_ = FiniteAlgebra._≟_ 𝑭ₛ

    Nₛ     = FiniteAlgebra.card 𝑭ₛ
    enumₛ  = FiniteAlgebra.enum 𝑭ₛ
    surₛ   = FiniteAlgebra.enum-sur 𝑭ₛ

    Πfin : FiniteAlgebra Π𝑮
    Πfin = power-FiniteAlgebra {n = n} 𝑭ₛ

    Nᴾ     = FiniteAlgebra.card Πfin
    enumᴾ  = FiniteAlgebra.enum Πfin
    surᴾ   = FiniteAlgebra.enum-sur Πfin

    s₀ : 𝕌[ 𝑺 ]
    s₀ = elt nas

    s₀≉ε : ¬ s₀ ≈ ε
    s₀≉ε = elt≉ε nas
```

Two membership facts used throughout: the diagonal tuples are members, and the power identity is a member.

```agda
  -- Every diagonal tuple κ g is a member of U.
  κ∈U : ∀ g → κ g ∈ U
  κ∈U g = D⊆U (κ-diag g)

  -- The identity tuple is a member of U.
  εᴾ∈U : εᴾ ∈ U
  εᴾ∈U = U-resp (λ t → ≈sym (e-pointwise t)) (κ∈U ε)
```

The commutator of the power is computed coordinatewise, by the three pointwise laws of [Classical.Structures.Group.Power][].

```agda
  -- The power commutator acts coordinatewise.
  comm-pointwise : ∀ x y t → commᴾ x y t ≈ comm (x t) (y t)
  comm-pointwise x y t = begin
    commᴾ x y t                            ≈⟨ ⊗-pointwise (x ⊗ y ⊗ invᴾ x) (invᴾ y) t ⟩
    (x ⊗ y ⊗ invᴾ x) t ∙ invᴾ y t          ≈⟨ ∙-cong (⊗-pointwise (x ⊗ y) (invᴾ x) t)
                                                     (inv-pointwise y t) ⟩
    (x ⊗ y) t ∙ invᴾ x t ∙ (y t) ⁻¹        ≈⟨ ∙-cong (∙-cong (⊗-pointwise x y t)
                                                             (inv-pointwise x t)) ≈refl ⟩
    comm (x t) (y t)                       ∎
```

#### The joint kernel of the subgroup

Two coordinates are **jointly identified** by `U` when every member takes equal values at them.  This is the kernel meet of the members read as functions of the coordinate, and it is the partition the theorem produces.

```agda
  infix 4 _~_

  -- i ~ j: every member of U agrees at i and j.
  _~_ : Fin n → Fin n → Type 0ℓ
  i ~ j = ∀ u → u ∈ U → u i ≈ u j
```

The relation is an equivalence, by the corresponding laws of the base setoid.

```agda
  -- Reflexivity, symmetry, and transitivity of the joint kernel.
  ~-refl : ∀ i → i ~ i
  ~-refl i u _ = ≈refl

  ~-sym : ∀ {i j} → i ~ j → j ~ i
  ~-sym p u u∈U = ≈sym (p u u∈U)

  ~-trans : ∀ {i j k} → i ~ j → j ~ k → i ~ k
  ~-trans p q u u∈U = ≈trans (p u u∈U) (q u u∈U)
```

Deciding the joint kernel is the first of the finite searches: the universal quantifier over members reduces to the power enumeration, because membership respects the pointwise equality.

```agda
  -- The joint kernel is decidable, by enumerating the power.
  ~-dec : ∀ i j → Dec (i ~ j)
  ~-dec i j = map′ toSem fromSem
    (all? (λ ν → U-dec (enumᴾ ν) →-dec (enumᴾ ν i ≟ₛ enumᴾ ν j)))
    where
    toSem : (∀ ν → enumᴾ ν ∈ U → enumᴾ ν i ≈ enumᴾ ν j) → i ~ j
    toSem h u u∈U =
      ≈trans (≈sym (e i)) (≈trans (h ν (U-resp (≈ᴾ-sym e) u∈U)) (e j))
      where
      ν = surᴾ u .proj₁
      e : enumᴾ ν ≈ᴾ u
      e = surᴾ u .proj₂

    fromSem : i ~ j → ∀ ν → enumᴾ ν ∈ U → enumᴾ ν i ≈ enumᴾ ν j
    fromSem h ν mem = h (enumᴾ ν) mem
```

#### Least representatives and the parent vector

Each coordinate is assigned the least coordinate equivalent to it; the smallest-witness search of the standard library produces the representative together with its minimality certificate.

```agda
  -- The least equivalent coordinate, with its two certificates.
  minRepΣ : (i : Fin n)
    → Σ[ r ∈ Fin n ] (r ~ i × ((l : Fin′ r) → ¬ (inject l ~ i)))
  minRepΣ i = r , decidable-stable (~-dec r i) r~~i , least
    where
    search = ¬∀⟶∃¬-smallest n (λ k → ¬ (k ~ i)) (λ k → ¬? (~-dec k i))
               (λ all¬ → all¬ i (~-refl i))
    r      = search .proj₁
    r~~i   = search .proj₂ .proj₁
    least  = search .proj₂ .proj₂

  -- The representative and its two certificates, named.
  minRep : Fin n → Fin n
  minRep i = minRepΣ i .proj₁

  minRep-~ : ∀ i → minRep i ~ i
  minRep-~ i = minRepΣ i .proj₂ .proj₁

  minRep-least : ∀ i (l : Fin′ (minRep i)) → ¬ (inject l ~ i)
  minRep-least i = minRepΣ i .proj₂ .proj₂
```

Equivalent coordinates receive the same representative: two least elements of the same equivalence class coincide, by trichotomy on their positions and the minimality certificates.

```agda
  -- The representative is constant on equivalence classes.
  minRep-cong : ∀ {i j} → i ~ j → minRep i ≡ minRep j
  minRep-cong {i} {j} i~j =
    decide (<-cmp (toℕ (minRep i)) (toℕ (minRep j)))
    where
    decide : Tri (toℕ (minRep i) < toℕ (minRep j))
                 (toℕ (minRep i) ≡ toℕ (minRep j))
                 (toℕ (minRep j) < toℕ (minRep i)) → minRep i ≡ minRep j
    decide (tri≈ _ e _) = toℕ-injective e
    decide (tri< lt _ _) =
      ⊥-elim (minRep-least j l (subst (_~ j) (≡sym l≡) (~-trans (minRep-~ i) i~j)))
      where
      l : Fin′ (minRep j)
      l = fromℕ< lt
      l≡ : inject l ≡ minRep i
      l≡ = toℕ-injective (≡trans (toℕ-inject l) (toℕ-fromℕ< lt))
    decide (tri> _ _ gt) =
      ⊥-elim (minRep-least i l (subst (_~ i) (≡sym l≡) (~-trans (minRep-~ j) (~-sym i~j))))
      where
      l : Fin′ (minRep i)
      l = fromℕ< gt
      l≡ : inject l ≡ minRep j
      l≡ = toℕ-injective (≡trans (toℕ-inject l) (toℕ-fromℕ< gt))
```

The parent vector tabulates the representatives, and its block relation is exactly the joint kernel: forward by constancy of the representative, backward through the representative's own equivalences.

```agda
  -- The computed partition: each coordinate points at its representative.
  π : ParentVec n
  π = tabulate minRep

  -- The tabulation lookup, once and for all.
  parent-π : ∀ i → parent π i ≡ minRep i
  parent-π i = lookup∘tabulate minRep i

  -- The block relation of π is the joint kernel (forward) ...
  ~→sameBlock : ∀ {i j} → i ~ j → SameBlock π i j
  ~→sameBlock {i} {j} i~j =
    ≡trans (parent-π i) (≡trans (minRep-cong i~j) (≡sym (parent-π j)))

  -- ... and (backward).
  sameBlock→~ : ∀ {i j} → SameBlock π i j → i ~ j
  sameBlock→~ {i} {j} sb =
    ~-trans (~-sym (minRep-~ i))
      (subst (_~ j) mr≡ (minRep-~ j))
    where
    mr≡ : minRep j ≡ minRep i
    mr≡ = ≡trans (≡sym (parent-π j)) (≡trans (≡sym sb) (parent-π i))
```

The first containment of the theorem is now the definition unwinding: a member of `U` is constant on the blocks of the joint kernel.

```agda
  -- U is contained in the partition subgroup of its joint kernel.
  U⊆Kπ : U ⊆ K π
  U⊆Kπ {u} u∈U {i} {j} sb = sameBlock→~ sb u u∈U
```

#### Killed projections

For a coordinate set `T` and a target coordinate `i`, the **killed projection** collects the values at `i` of members of `U` that vanish on `T`.  Members enter through the power enumeration, so the collection is a level-zero predicate on the base carrier regardless of `T`, and closure under the group operations needs no decision procedure.

```agda
  module KilledProj (T : Pred (Fin n) 0ℓ) (i : Fin n) where

    -- The projection: values at i of members vanishing on T.
    KP : Pred 𝕌[ 𝑺 ] 0ℓ
    KP s = Σ[ ν ∈ Fin Nᴾ ]
             (enumᴾ ν ∈ U × (∀ t → t ∈ T → enumᴾ ν t ≈ ε) × enumᴾ ν i ≈ s)
```

The constructor: any member vanishing on `T` puts its value at `i` into the projection, after a pass through the enumeration.

```agda
    -- Membership from an arbitrary member of U vanishing on T.
    KP-intro : ∀ u → u ∈ U → (∀ t → t ∈ T → u t ≈ ε) → ∀ {s} → u i ≈ s → KP s
    KP-intro u u∈U kills {s} ui≈s =
      ν , U-resp (≈ᴾ-sym e) u∈U
        , (λ t t∈T → ≈trans (e t) (kills t t∈T))
        , ≈trans (e i) ui≈s
      where
      ν = surᴾ u .proj₁
      e : enumᴾ ν ≈ᴾ u
      e = surᴾ u .proj₂
```

The projection is an equality-respecting subgroup: products, the identity, and inverses of members vanishing on `T` vanish on `T`, coordinatewise.

```agda
    -- The projection respects the base equality.
    KP-respects : ∀ {s s'} → s ≈ s' → KP s → KP s'
    KP-respects e (ν , mem , kills , val) = ν , mem , kills , ≈trans val e

    -- The projection is closed under the three group operations.
    KP-∙ : ∀ {s s'} → KP s → KP s' → KP (s ∙ s')
    KP-∙ {s} {s'} (ν , mem , kills , val) (ν' , mem' , kills' , val') =
      KP-intro (enumᴾ ν ⊗ enumᴾ ν') (U-∙ mem mem')
        (λ t t∈T → ≈trans (⊗-pointwise (enumᴾ ν) (enumᴾ ν') t)
                     (≈trans (∙-cong (kills t t∈T) (kills' t t∈T)) (idˡ-law ε)))
        (≈trans (⊗-pointwise (enumᴾ ν) (enumᴾ ν') i) (∙-cong val val'))

    KP-ε : KP ε
    KP-ε = KP-intro εᴾ εᴾ∈U (λ t _ → e-pointwise t) (e-pointwise i)

    KP-⁻¹ : ∀ {s} → KP s → KP (s ⁻¹)
    KP-⁻¹ {s} (ν , mem , kills , val) =
      KP-intro (invᴾ (enumᴾ ν)) (U-inv mem)
        (λ t t∈T → ≈trans (inv-pointwise (enumᴾ ν) t)
                     (≈trans (⁻¹-cong (kills t t∈T)) ε⁻¹≈ε))
        (≈trans (inv-pointwise (enumᴾ ν) i) (⁻¹-cong val))
```

Normality is conjugation by a diagonal tuple: the diagonal is in `U`, conjugating preserves both the vanishing set and membership, and at `i` it conjugates the value.

```agda
    -- The projection is normalized by conjugation.
    KP-normal : ∀ g {s} → KP s → KP (g ∙ s ∙ g ⁻¹)
    KP-normal g {s} (ν , mem , kills , val) =
      KP-intro w (U-∙ (U-∙ (κ∈U g) mem) (U-inv (κ∈U g)))
        (λ t t∈T → ≈trans (w-pt t)
                     (≈trans (∙-cong (∙-cong ≈refl (kills t t∈T)) ≈refl)
                       (≈trans (∙-cong (idʳ-law g) ≈refl) (invʳ-law g))))
        (≈trans (w-pt i) (∙-cong (∙-cong ≈refl val) ≈refl))
      where
      w = κ g ⊗ enumᴾ ν ⊗ invᴾ (κ g)

      w-pt : ∀ t → w t ≈ g ∙ enumᴾ ν t ∙ g ⁻¹
      w-pt t = ≈trans (⊗-pointwise (κ g ⊗ enumᴾ ν) (invᴾ (κ g)) t)
                 (∙-cong (⊗-pointwise (κ g) (enumᴾ ν) t) (inv-pointwise (κ g) t))

    -- The packaged normal subgroup.
    KP-nsg : IsNormalSubgroup KP
    KP-nsg .isSubgroup =
      mkIsSubgroup 𝒮 (λ {s} {s'} → KP-respects {s} {s'})
        (λ {s} {s'} → KP-∙ {s} {s'}) KP-ε (λ {s} → KP-⁻¹ {s})
    KP-nsg .isNormal g {s} = KP-normal g {s}
```

Simplicity turns one nontrivial member into all of them: this is the only way the projection is ever consumed.

```agda
    -- A member of U vanishing on T and nontrivial at i makes the projection full.
    KP-full : ∀ w → w ∈ U → (∀ t → t ∈ T → w t ≈ ε) → ¬ (w i ≈ ε) → ∀ s → KP s
    KP-full w w∈U kills wi≉ε =
      simple nas KP KP-nsg (w i , KP-intro w w∈U kills ≈refl , wi≉ε)
```

#### Separation

Inequivalent coordinates are separated by a member of `U`, found by the enumeration search; dividing off the diagonal tuple of its value at `j` renormalizes the separator to vanish at `j` while staying away from the identity at `i`.

```agda
  -- A separator: it vanishes at j and not at i.
  separator : ∀ {i j} → ¬ (i ~ j)
    → Σ[ w ∈ 𝕌[ Π𝑮 ] ] (w ∈ U × w j ≈ ε × ¬ (w i ≈ ε))
  separator {i} {j} ¬ij = w , w∈U , wj≈ε , wi≉ε
    where
    ¬all : ¬ (∀ ν → enumᴾ ν ∈ U → enumᴾ ν i ≈ enumᴾ ν j)
    ¬all h = ¬ij λ u u∈U →
      ≈trans (≈sym (surᴾ u .proj₂ i))
        (≈trans (h (surᴾ u .proj₁) (U-resp (≈ᴾ-sym (surᴾ u .proj₂)) u∈U))
          (surᴾ u .proj₂ j))

    found = ¬∀⟶∃¬ Nᴾ (λ ν → enumᴾ ν ∈ U → enumᴾ ν i ≈ enumᴾ ν j)
              (λ ν → U-dec (enumᴾ ν) →-dec (enumᴾ ν i ≟ₛ enumᴾ ν j)) ¬all

    u₀ = enumᴾ (found .proj₁)

    u₀∈U : u₀ ∈ U
    u₀∈U = decide (U-dec u₀)
      where
      decide : Dec (u₀ ∈ U) → u₀ ∈ U
      decide (yes p) = p
      decide (no ¬p) = ⊥-elim (found .proj₂ (λ mem → ⊥-elim (¬p mem)))

    ¬agree : ¬ (u₀ i ≈ u₀ j)
    ¬agree e = found .proj₂ (λ _ → e)

    w = u₀ ⊗ invᴾ (κ (u₀ j))

    w-pt : ∀ t → w t ≈ u₀ t ∙ (u₀ j) ⁻¹
    w-pt t = ≈trans (⊗-pointwise u₀ (invᴾ (κ (u₀ j))) t)
               (∙-cong ≈refl (inv-pointwise (κ (u₀ j)) t))

    w∈U : w ∈ U
    w∈U = U-∙ u₀∈U (U-inv (κ∈U (u₀ j)))

    wj≈ε : w j ≈ ε
    wj≈ε = ≈trans (w-pt j) (invʳ-law (u₀ j))

    wi≉ε : ¬ (w i ≈ ε)
    wi≉ε h = ¬agree (∙⁻¹≈ε→≈ (≈trans (≈sym (w-pt i)) h))
```

Separation feeds the killed projection at the singleton `{j}`, and simplicity upgrades one separator to a separator with *any prescribed value* at `i`.

```agda
  -- Members of U vanishing at j realize every value at i.
  axis-full : ∀ {i j} → ¬ (i ~ j)
    → ∀ v → Σ[ u ∈ 𝕌[ Π𝑮 ] ] (u ∈ U × u j ≈ ε × u i ≈ v)
  axis-full {i} {j} ¬ij v =
    enumᴾ (kp .proj₁) , kp .proj₂ .proj₁
      , kp .proj₂ .proj₂ .proj₁ j refl
      , kp .proj₂ .proj₂ .proj₂
    where
    open KilledProj (_≡ j) i

    sep = separator {i} {j} ¬ij

    kp : KP v
    kp = KP-full (sep .proj₁) (sep .proj₂ .proj₁)
           (λ t t≡j → subst (λ z → sep .proj₁ z ≈ ε) (≡sym t≡j)
                        (sep .proj₂ .proj₂ .proj₁))
           (sep .proj₂ .proj₂ .proj₂) v
```

#### The non-commuting partner

The support-shrinking iteration needs, for a value `d` away from the identity, a partner that fails to commute with it.  Triviality of the center of the nonabelian simple base supplies one, and the finite search finds it.

```agda
  -- Every non-identity element has a non-commuting partner.
  noncommuting-partner : ∀ {d} → ¬ (d ≈ ε) → Σ[ g ∈ 𝕌[ 𝑺 ] ] ¬ Commutes d g
  noncommuting-partner {d} d≉ε =
    enumₛ (found .proj₁) , found .proj₂
    where
    ¬all : ¬ (∀ ν → Commutes d (enumₛ ν))
    ¬all h = d≉ε (center-trivial (≈-dec→Stable-≈ε _≟ₛ_) nas d central)
      where
      central : d ∈ center
      central x _ = Commutes-congʳ (surₛ x .proj₂) (h (surₛ x .proj₁))

    found = ¬∀⟶∃¬ Nₛ (λ ν → Commutes d (enumₛ ν))
              (λ ν → (d ∙ enumₛ ν) ≟ₛ (enumₛ ν ∙ d)) ¬all
```

#### Support shrinking

The iteration: walking a list of coordinates outside the block of `i`, each step commutes the accumulated member against a member that vanishes at the next coordinate and carries a non-commuting partner value at `i`.  The commutator vanishes wherever either factor does, so the processed coordinates stay dead, and the partner choice keeps the value at `i` alive.

```agda
  -- One member of U per block: supported in the block of i, nontrivial at i.
  block-support : ∀ i
    → Σ[ a ∈ 𝕌[ Π𝑮 ] ] (a ∈ U × (∀ t → ¬ (i ~ t) → a t ≈ ε) × ¬ (a i ≈ ε))
  block-support i =
    a , a∈U
      , (λ t ¬it → kills t (∈-filter⁺ (λ t' → ¬? (~-dec i t')) (∈-allFin t) ¬it))
      , ai≉ε
    where
    kill : (L : List (Fin n)) → (∀ t → t ∈ˡ L → ¬ (i ~ t))
      → Σ[ a ∈ 𝕌[ Π𝑮 ] ] (a ∈ U × (∀ t → t ∈ˡ L → a t ≈ ε) × ¬ (a i ≈ ε))
    kill [] _ = κ s₀ , κ∈U s₀ , (λ t ()) , s₀≉ε
    kill (j ∷ L) outside = a' , a'∈U , kills' , a'i≉ε
      where
      prev = kill L (λ t t∈L → outside t (there t∈L))
      a     = prev .proj₁
      a∈U   = prev .proj₂ .proj₁
      kills = prev .proj₂ .proj₂ .proj₁
      ai≉ε  = prev .proj₂ .proj₂ .proj₂

      partner = noncommuting-partner ai≉ε
      g   = partner .proj₁
      ¬cm = partner .proj₂

      axis = axis-full (outside j (here refl)) g
      w     = axis .proj₁
      w∈U   = axis .proj₂ .proj₁
      wj≈ε  = axis .proj₂ .proj₂ .proj₁
      wi≈g  = axis .proj₂ .proj₂ .proj₂

      a' = commᴾ a w

      a'∈U : a' ∈ U
      a'∈U = U-∙ (U-∙ (U-∙ a∈U w∈U) (U-inv a∈U)) (U-inv w∈U)

      kills' : ∀ t → t ∈ˡ (j ∷ L) → a' t ≈ ε
      kills' t (here t≡j) =
        ≈trans (comm-pointwise a w t)
          (comm-εʳ (a t) (subst (λ z → w z ≈ ε) (≡sym t≡j) wj≈ε))
      kills' t (there t∈L) =
        ≈trans (comm-pointwise a w t) (comm-εˡ (w t) (kills t t∈L))

      a'i≉ε : ¬ (a' i ≈ ε)
      a'i≉ε h = ¬cm (Commutes-congʳ wi≈g
        (comm≈ε→commutes (a i) (w i) (≈trans (≈sym (comm-pointwise a w i)) h)))

    result = kill (filter (λ t → ¬? (~-dec i t)) (allFin n))
               (λ t t∈F → ∈-filter⁻ (λ t' → ¬? (~-dec i t')) {xs = allFin n} t∈F .proj₂)
    a     = result .proj₁
    a∈U   = result .proj₂ .proj₁
    kills = result .proj₂ .proj₂ .proj₁
    ai≉ε  = result .proj₂ .proj₂ .proj₂
```

#### Block columns

The **block column** of `r` with value `s` is the tuple carrying `s` on the block of `r` and the identity elsewhere.  Feeding the block-supported member to the killed projection at the complement of the block, simplicity realizes every value; the realizing member is constant on the block, because the block is a block of the joint kernel, so it *is* the column.

```agda
  -- The block column of r with value s.
  cB : Fin n → 𝕌[ 𝑺 ] → 𝕌[ Π𝑮 ]
  cB r s t = if does (minRep t ≟f minRep r) then s else ε

  -- Every block column is a member of U.
  column∈U : ∀ r s → cB r s ∈ U
  column∈U r s = U-resp u≈cB mem
    where
    open KilledProj (λ t → ¬ (r ~ t)) r

    seed = block-support r

    kp : KP s
    kp = KP-full (seed .proj₁) (seed .proj₂ .proj₁)
           (λ t ¬rt → seed .proj₂ .proj₂ .proj₁ t ¬rt)
           (seed .proj₂ .proj₂ .proj₂) s

    u = enumᴾ (kp .proj₁)

    mem : u ∈ U
    mem = kp .proj₂ .proj₁

    kills : ∀ t → ¬ (r ~ t) → u t ≈ ε
    kills = kp .proj₂ .proj₂ .proj₁

    ur≈s : u r ≈ s
    ur≈s = kp .proj₂ .proj₂ .proj₂

    u≈cB : ∀ t → u t ≈ cB r s t
    u≈cB t = decide (minRep t ≟f minRep r)
      where
      decide : Dec (minRep t ≡ minRep r) → u t ≈ cB r s t
      decide (yes e) =
        ≈trans (≈trans (t~r u mem) ur≈s)
          (reflexive (≡sym (cong (λ b → if b then s else ε) (dec-true (minRep t ≟f minRep r) e))))
        where
        t~r : t ~ r
        t~r = ~-trans (~-sym (minRep-~ t)) (subst (_~ r) (≡sym e) (minRep-~ r))
      decide (no ne) =
        ≈trans (kills t (λ r~t → ne (≡sym (minRep-cong r~t))))
          (reflexive (≡sym (cong (λ b → if b then s else ε) (dec-false (minRep t ≟f minRep r) ne))))
```

#### The fold: peeling block columns

For a member `y` of `K π`, the family `z k` replaces `y` by the identity on every block whose representative sits below `k`.  Stage `n` is the identity tuple, stage `0` is `y`, and each stage is the previous one times at most one block column, so membership in `U` descends from stage `n` to stage `0`.

```agda
  module _ (y : 𝕌[ Π𝑮 ]) (yK : y ∈ K π) where

    private
      -- Stage k of the peel: y with the blocks represented below k killed.
      z : ℕ → 𝕌[ Π𝑮 ]
      z k t = if does (toℕ (minRep t) <? k) then ε else y t
```

One peeling step.  If some coordinate's representative sits at exactly `k`, the stage differs from the next by the block column of that representative with the member's own value there, and the three-way position comparison at each coordinate verifies the pointwise identity; if none does, the stages agree pointwise.

```agda
      z-step : ∀ k → z (suc k) ∈ U → z k ∈ U
      z-step k zskU = go (any? (λ t → toℕ (minRep t) ≟ℕ k))
        where
        zk-eval-ε : ∀ {t} → toℕ (minRep t) < k → z k t ≡ ε
        zk-eval-ε {t} lt =
          cong (λ b → if b then ε else y t) (dec-true (toℕ (minRep t) <? k) lt)

        zk-eval-y : ∀ {t} → ¬ (toℕ (minRep t) < k) → z k t ≡ y t
        zk-eval-y {t} ¬lt =
          cong (λ b → if b then ε else y t) (dec-false (toℕ (minRep t) <? k) ¬lt)

        zsk-eval-ε : ∀ {t} → toℕ (minRep t) < suc k → z (suc k) t ≡ ε
        zsk-eval-ε {t} lt =
          cong (λ b → if b then ε else y t) (dec-true (toℕ (minRep t) <? suc k) lt)

        zsk-eval-y : ∀ {t} → ¬ (toℕ (minRep t) < suc k) → z (suc k) t ≡ y t
        zsk-eval-y {t} ¬lt =
          cong (λ b → if b then ε else y t) (dec-false (toℕ (minRep t) <? suc k) ¬lt)

        go : Dec (∃ λ t → toℕ (minRep t) ≡ k) → z k ∈ U
        go (yes (t₀ , e₀)) =
          U-resp pw (U-∙ (column∈U t₀ (y t₀)) zskU)
          where
          cB-eval-s : ∀ {t} → minRep t ≡ minRep t₀ → cB t₀ (y t₀) t ≡ y t₀
          cB-eval-s {t} e =
            cong (λ b → if b then y t₀ else ε) (dec-true (minRep t ≟f minRep t₀) e)

          cB-eval-ε : ∀ {t} → ¬ (minRep t ≡ minRep t₀) → cB t₀ (y t₀) t ≡ ε
          cB-eval-ε {t} ne =
            cong (λ b → if b then y t₀ else ε) (dec-false (minRep t ≟f minRep t₀) ne)

          pw : ∀ t → (cB t₀ (y t₀) ⊗ z (suc k)) t ≈ z k t
          pw t = ≈trans (⊗-pointwise (cB t₀ (y t₀)) (z (suc k)) t)
                        (branch (<-cmp (toℕ (minRep t)) k))
            where
            branch : Tri (toℕ (minRep t) < k) (toℕ (minRep t) ≡ k) (k < toℕ (minRep t))
              → cB t₀ (y t₀) t ∙ z (suc k) t ≈ z k t
            branch (tri< lt _ _) =
              ≈trans (∙-cong (reflexive (cB-eval-ε ne)) (reflexive (zsk-eval-ε (m<n⇒m<1+n lt))))
                (≈trans (idˡ-law ε) (reflexive (≡sym (zk-eval-ε lt))))
              where
              ne : ¬ (minRep t ≡ minRep t₀)
              ne e = <-irrefl (≡trans (cong toℕ e) e₀) lt
            branch (tri≈ ¬lt e _) =
              ≈trans (∙-cong (reflexive (cB-eval-s mr≡)) (reflexive (zsk-eval-ε m<sk)))
                (≈trans (idʳ-law (y t₀))
                  (≈trans (yK sb) (reflexive (≡sym (zk-eval-y ¬lt)))))
              where
              mr≡ : minRep t ≡ minRep t₀
              mr≡ = toℕ-injective (≡trans e (≡sym e₀))
              m<sk : toℕ (minRep t) < suc k
              m<sk = s≤s (≤-reflexive e)
              sb : SameBlock π t₀ t
              sb = ≡trans (parent-π t₀) (≡trans (≡sym mr≡) (≡sym (parent-π t)))
            branch (tri> ¬lt _ gt) =
              ≈trans (∙-cong (reflexive (cB-eval-ε ne)) (reflexive (zsk-eval-y ¬msk)))
                (≈trans (idˡ-law (y t)) (reflexive (≡sym (zk-eval-y ¬lt))))
              where
              ne : ¬ (minRep t ≡ minRep t₀)
              ne e = <-irrefl (≡sym (≡trans (cong toℕ e) e₀)) gt
              ¬msk : ¬ (toℕ (minRep t) < suc k)
              ¬msk = ≤⇒≯ gt
        go (no ¬ex) = U-resp pw zskU
          where
          pw : ∀ t → z (suc k) t ≈ z k t
          pw t = branch (<-cmp (toℕ (minRep t)) k)
            where
            branch : Tri (toℕ (minRep t) < k) (toℕ (minRep t) ≡ k) (k < toℕ (minRep t))
              → z (suc k) t ≈ z k t
            branch (tri< lt _ _) =
              reflexive (≡trans (zsk-eval-ε (m<n⇒m<1+n lt)) (≡sym (zk-eval-ε lt)))
            branch (tri≈ _ e _) = ⊥-elim (¬ex (t , e))
            branch (tri> ¬lt _ gt) =
              reflexive (≡trans (zsk-eval-y (≤⇒≯ gt)) (≡sym (zk-eval-y ¬lt)))
```

The endpoints of the peel: stage `n` is the identity tuple because every representative sits below `n`, and stage `0` is `y` itself because nothing sits below `0`.

```agda
      z-base : z n ∈ U
      z-base = U-resp pw εᴾ∈U
        where
        pw : ∀ t → εᴾ t ≈ z n t
        pw t = ≈trans (e-pointwise t)
          (reflexive (≡sym (cong (λ b → if b then ε else y t)
            (dec-true (toℕ (minRep t) <? n) (toℕ<n (minRep t))))))

      down : ∀ m k → m + k ≡ n → z k ∈ U
      down zero k eq = subst (λ q → z q ∈ U) (≡sym eq) z-base
      down (suc m) k eq =
        z-step k (down m (suc k) (≡trans (+-suc m k) eq))
```

Assembled: the member of `K π` is stage `0` of its own peel.

```agda
    -- Every member of the partition subgroup of the joint kernel is in U.
    peel : y ∈ U
    peel = U-resp (λ t → ≈refl) (down n 0 (+-identityʳ n))
```

#### The theorem

The two containments, packaged in the Σ-form the FLRP consumers unwrap.

```agda
  -- The second containment, from the fold.
  Kπ⊆U : K π ⊆ U
  Kπ⊆U {y} yK = peel y yK

  -- Kurzweil's surjectivity lemma, decidable form: U is a partition subgroup.
  collapse : Σ[ p ∈ ParentVec n ] ((U ⊆ K p) × (K p ⊆ U))
  collapse = π , U⊆Kπ , Kπ⊆U
```
