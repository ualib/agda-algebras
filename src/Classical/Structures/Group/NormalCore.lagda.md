---
layout: default
file: "src/Classical/Structures/Group/NormalCore.lagda.md"
title: "Classical.Structures.Group.NormalCore module"
date: "2026-07-11"
author: "the agda-algebras development team"
---

### The normal core of a subgroup

This is the [Classical.Structures.Group.NormalCore][] module of the [Agda Universal Algebra Library][].

For a subgroup `H` of a group `𝑮`, the **normal core** `Core_G(H)` is the largest
normal subgroup of `𝑮` contained in `H`.

Classically the normal core is the intersection `⋂ { g H g⁻¹ ∣ g ∈ G }` of all
conjugates of `H`.  We define it *constructively* as that intersection using the
infinitary meet `⨅`{.AgdaFunction} of the subuniverse lattice of
[Setoid.Subalgebras.CompleteLattice][] over the family of conjugates from
[Classical.Structures.Group.Conjugation][]; so the definition is an instance of
the complete-lattice machinery rather than an ad-hoc predicate.

**Note on the universe levels**.  The lattice is instantiated at universe level
`ℓ₀ = α ⊔ ρ ⊔ ℓ`, the absorbing level for group-theoretic constructions over a
`Group α ρ` and a subgroup predicate at level `ℓ`: conjugates mention the setoid
equality (level `ρ`) and the predicate (level `ℓ`), and the meet is indexed by the
carrier (level `α`), lifted by `Lift (ρ ⊔ ℓ)` to reach the index level of
`⨅`{.AgdaFunction}.

The module proves that the normal core

+ is contained in `H` (`core-⊆`{.AgdaFunction}),
+ is a subgroup (`core-isSubgroup`{.AgdaFunction}),
+ is normal (`core-normal`{.AgdaFunction}), and
+ contains every normal subgroup contained in `H` (`core-greatest`{.AgdaFunction}).

The conclusion is that the core is the greatest normal subgroup below `H`.[^1]

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.NormalCore where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Product     using ( _,_ ; proj₁ ; proj₂ ; ∃-syntax ; _×_)
open import Level            using ( Level ; _⊔_ ; Lift ; lift ; lower )
open import Relation.Binary  using ( Setoid )
open import Relation.Unary   using ( Pred ; _∈_ ; _⊆_ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Group.Basic        using ( Group ; module Group-Op )
open import Classical.Structures.Group.Subgroups    using ( IsSubgroup )
open import Classical.Structures.Group.Conjugation  using ( module Conjugate )
open import Setoid.Algebras.Basic                   using ( 𝔻[_] ; 𝕌[_] )
open import Setoid.Subalgebras.CompleteLattice      using ( module Sublattice )
```
-->

#### The construction

`Core 𝑮 H H-isSubgroup` packages the normal core of the subgroup `H` in `G`.
The family `conjugates`{.AgdaFunction} sends (the lift of) a group element `g` to
the conjugate subgroup `g H g⁻¹` as an element of the subuniverse lattice, and
`core`{.AgdaFunction} is the lattice meet of that family; its underlying predicate
is definitionally the intersection `⋂ g (conjugate g H)`.

```agda
module Core {α ρ : Level} (𝒢@(𝑮 , _) : Group α ρ) {ℓ : Level}
  (H : Pred 𝕌[ 𝑮 ] ℓ) (H-isSubgroup : IsSubgroup 𝒢 H)
  where

  open Setoid 𝔻[ 𝑮 ]  using ( _≈_ ) renaming ( sym to ≈sym )
  open SetoidReasoning 𝔻[ 𝑮 ]
  open Group-Op 𝒢 using ( _∙_ ; ε ; _⁻¹ )
  open Conjugate 𝒢
  open Sublattice 𝑮 (α ⊔ ρ ⊔ ℓ) using ( Subᴸ ; ⨅ )
  open IsSubgroup H-isSubgroup renaming  (respects to H-respects
                                         ; isSubuniverse to H-isSubuniverse)

  -- The index of the meet: the carrier, lifted to the lattice's index level.
  Index : Type (α ⊔ ρ ⊔ ℓ)
  Index = Lift (ρ ⊔ ℓ) 𝕌[ 𝑮 ]

  -- The family of all conjugates of H, as elements of the subuniverse lattice.
  conjugates : Index → Subᴸ
  conjugates i =  [ H ]^ lower i , conjugate-isSubuniverse (lower i) H H-isSubuniverse

  -- The normal core: the complete-lattice meet (intersection) of all conjugates of H.
  core : Subᴸ
  core = ⨅ conjugates
```

#### Membership characterization

Unwinding the definition, `x` lies in the core precisely when every conjugate
`x ^ g` lies in `H`; the two lemmas below convert between the definitional form
(a witness in each conjugate subgroup) and this pointwise form, which is the
convenient one in proofs.

```agda
  -- If x is in the core then all its conjugates are in H.
  core-mem-conj : {x : 𝕌[ 𝑮 ]} → x ∈ core .proj₁ → ∀ g → x ^ g ∈ H
  core-mem-conj {x} x∈core g = H-respects (≈sym conj-g-x≈h) h∈H
    where
    h : 𝕌[ 𝑮 ]
    h = x∈core (lift (g ⁻¹)) .proj₁

    h∈H : h ∈ H
    h∈H = x∈core (lift (g ⁻¹)) .proj₂ .proj₁

    x≈conj : x ≈ conj (g ⁻¹) h
    x≈conj = x∈core (lift (g ⁻¹)) .proj₂ .proj₂

    conj-g-x≈h : conj g x ≈ h
    conj-g-x≈h = begin
      conj g x                ≈⟨ conj-cong g x≈conj ⟩
      conj g (conj (g ⁻¹) h)  ≈⟨ conj-conj⁻¹ g h ⟩
      h                       ∎

  -- Conversely, if all conjugates of x are in H then x is in the core.
  conj-mem-core : {x : 𝕌[ 𝑮 ]} → (∀ g → conj g x ∈ H) → x ∈ proj₁ core
  conj-mem-core {x} cm i =
    conj (lower i ⁻¹) x , cm (lower i ⁻¹) , ≈sym (conj-conj⁻¹ (lower i) x)
```

#### The core is a normal subgroup contained in `H`

The **normal core** of `H` is the intersection of all conjugates of `H`.  These four
results are its defining properties, and together they say it is the largest normal
subgroup that `H` contains.

+  `core-⊆`{.AgdaFunction}: the core sits inside `H`, obtained by instantiating the
   conjugate at `g = ε`.
+  `core-isSubgroup`{.AgdaFunction}: it is an (equality-respecting) subgroup.
   The equality-respecting holds componentwise, and closure comes from the
   subuniverse machinery, an intersection of subuniverses being a subuniverse.
+  `core-normal`{.AgdaFunction}: it is normal, because conjugating a member by
   `g` leaves every conjugate inside `H`: `(x ^ g)^ k` is the `k ∙ g`-conjugate
   of `x`.
+  `core-greatest`{.AgdaFunction}: it is the greatest normal subgroup in `H`,
   since any normal subset of `H` lies inside every conjugate of `H` and hence
   inside the intersection.

The last is what makes the core a *construction* rather than merely a subgroup: it
is characterised by a universal property, so it's determined up to mutual inclusion.
Any two predicates with these four properties contain one another; in this
intensional setting that is the strongest uniqueness on offer, since mutual
inclusion does not make two predicates definitionally equal.

```agda
  -- The core is contained in H (instantiate the conjugate at g = ε).
  core-⊆ : core .proj₁ ⊆ H
  core-⊆ {x} x∈core = H-respects (conj-action-ε x) (core-mem-conj x∈core ε)

  -- The core is an equality-respecting subgroup: respect holds componentwise
  -- (each conjugate respects ≈ by construction), and the meet of subuniverses
  -- is a subuniverse by the lattice machinery.
  core-isSubgroup : IsSubgroup 𝒢 (proj₁ core)
  core-isSubgroup = record
    { respects = λ x≈y x∈core i → conjugate-respects (lower i) H x≈y (x∈core i)
    ; isSubuniverse = core .proj₂
    }

  -- The core is normal: conjugating a member by g keeps every conjugate in H,
  -- since (x ^ g)^k is the (k ∙ g)-conjugate of x.
  core-normal : IsNormal (proj₁ core)
  core-normal g {x} x∈core =
    conj-mem-core λ k → H-respects (conj-action-∙ k g x) (core-mem-conj x∈core (k ∙ g))

  -- The core is the greatest normal subgroup contained in H: any normal subset
  -- of H sits inside every conjugate of H, hence inside the meet.
  core-greatest : {ℓⁿ : Level} {N : Pred 𝕌[ 𝑮 ] ℓⁿ}
    →  IsNormal N → N ⊆ H → N ⊆ core .proj₁
  core-greatest N-normal N⊆H x∈N = conj-mem-core λ g → N⊆H (N-normal g x∈N)
```

---
[^1]:   This is the normalization step behind the core-free reduction
        `[H, G] ≅ [H/N, G/N]` of the FLRP program (see
        `docs/notes/flrp-research-roadmap.md` § 4).
