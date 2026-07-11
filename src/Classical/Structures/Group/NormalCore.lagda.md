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
normal subgroup of `𝑮` contained in `H`; classically it is the intersection
`⋂ { g H g⁻¹ ∣ g ∈ G }` of all conjugates of `H`.  We define it *constructively as
that intersection*, using the infinitary meet `⨅`{.AgdaFunction} of the subuniverse
lattice of [Setoid.Subalgebras.CompleteLattice][] over the family of conjugates from
[Classical.Structures.Group.Conjugation][] — so the definition is an instance of the
complete-lattice machinery rather than an ad-hoc predicate.

The lattice is instantiated at base level `ℓ₀ = α ⊔ ρ ⊔ ℓ`, the absorbing level for
group-theoretic constructions over a `Group α ρ` and a subgroup predicate at level
`ℓ`: conjugates mention the setoid equality (level `ρ`) and the predicate (level
`ℓ`), and the meet is indexed by the carrier (level `α`), lifted by
`Lift (ρ ⊔ ℓ)` to reach the index level of `⨅`{.AgdaFunction}.

The module proves the characteristic properties as small named lemmas, in
particular that the core is contained in `H` (`core-⊆`{.AgdaFunction}), is an
equality-respecting subgroup (`core-isSubgroup`{.AgdaFunction}), is normal
(`core-normal`{.AgdaFunction}), and contains every normal subgroup contained in `H`
(`core-greatest`{.AgdaFunction}) — together: the core is the *greatest* normal
subgroup below `H`.  This is the normalization step behind the core-free reduction
`[H, G] ≅ [H/N, G/N]` of the FLRP program (see
`docs/notes/flrp-research-roadmap.md` § 4).

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.NormalCore where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Product                  using ( _,_ ; proj₁ ; proj₂ )
open import Level                         using ( Level ; _⊔_ ; Lift ; lift ; lower )
open import Relation.Binary               using ( Setoid )
open import Relation.Binary.Definitions   using ( _Respects_ )
open import Relation.Unary                using ( Pred ; _∈_ ; _⊆_ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Signatures.Group             using ( Sig-Group )
open import Classical.Structures.Group             using ( Group ; module Group-Op )
open import Classical.Structures.Group.Subgroups   using ( IsSubgroup )
open import Classical.Structures.Group.Conjugation using ( module Conj )

open import Setoid.Algebras.Basic {𝑆 = Sig-Group}              using ( Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Subalgebras.CompleteLattice {𝑆 = Sig-Group} using ( module Sublattice )
```
-->

#### The construction

`Core 𝑮 H H-isSubgroup` packages the normal core of the subgroup cut out by `H`.
The family `conjugates`{.AgdaFunction} sends (the lift of) a group element `g` to
the conjugate subgroup `g H g⁻¹` as an element of the subuniverse lattice, and
`core`{.AgdaFunction} is the lattice meet of that family — its underlying predicate
is definitionally the intersection `⋂ g (conjugate g H)`.

```agda
module Core {α ρ : Level} (𝑮 : Group α ρ) {ℓ : Level}
  (H : Pred 𝕌[ proj₁ 𝑮 ] ℓ) (H-isSubgroup : IsSubgroup 𝑮 H)
  where

  private
    𝑨 = proj₁ 𝑮
    A = 𝕌[ 𝑨 ]

  open Setoid 𝔻[ 𝑨 ]  using ( _≈_ ) renaming ( sym to ≈sym )
  open SetoidReasoning 𝔻[ 𝑨 ]
  open Group-Op 𝑮 using ( _∙_ ; ε ; _⁻¹ )
  open Conj 𝑮
    using ( conj ; conj-cong ; conj-action-∙ ; conj-action-ε ; conj-conj⁻¹
          ; conjugate ; conjugate-respects ; conjugate-isSubuniverse ; IsNormal )
  open Sublattice 𝑨 (α ⊔ ρ ⊔ ℓ) using ( Subᴸ ; ⨅ )

  private
    H-respects : H Respects _≈_
    H-respects = IsSubgroup.respects H-isSubgroup

  -- The index of the meet: the carrier, lifted to the lattice's index level.
  Index : Type (α ⊔ ρ ⊔ ℓ)
  Index = Lift (ρ ⊔ ℓ) A

  -- The family of all conjugates of H, as elements of the subuniverse lattice.
  conjugates : Index → Subᴸ
  conjugates i =  conjugate (lower i) H
               ,  conjugate-isSubuniverse (lower i) {B = H} (IsSubgroup.isSubuniverse H-isSubgroup)

  -- The normal core: the complete-lattice meet (intersection) of all conjugates of H.
  core : Subᴸ
  core = ⨅ conjugates
```

#### Membership characterization

Unwinding the definition, `x` lies in the core precisely when every conjugate
`conj g x` lies in `H`; the two lemmas below convert between the definitional form
(a witness in each conjugate subgroup) and this pointwise form, which is the
convenient one in proofs.

```agda
  -- If x is in the core then all its conjugates are in H.
  core-mem-conj : {x : A} → x ∈ proj₁ core → ∀ g → conj g x ∈ H
  core-mem-conj {x} x∈core g = H-respects (≈sym conj-g-x≈h) h∈H
    where
    h : A
    h = proj₁ (x∈core (lift (g ⁻¹)))

    h∈H : h ∈ H
    h∈H = proj₁ (proj₂ (x∈core (lift (g ⁻¹))))

    x≈conj : x ≈ conj (g ⁻¹) h
    x≈conj = proj₂ (proj₂ (x∈core (lift (g ⁻¹))))

    conj-g-x≈h : conj g x ≈ h
    conj-g-x≈h = begin
      conj g x                ≈⟨ conj-cong g x≈conj ⟩
      conj g (conj (g ⁻¹) h)  ≈⟨ conj-conj⁻¹ g h ⟩
      h                       ∎

  -- Conversely, if all conjugates of x are in H then x is in the core.
  conj-mem-core : {x : A} → (∀ g → conj g x ∈ H) → x ∈ proj₁ core
  conj-mem-core {x} cm i =
    conj (lower i ⁻¹) x , cm (lower i ⁻¹) , ≈sym (conj-conj⁻¹ (lower i) x)
```

#### The core is a normal subgroup contained in `H`

```agda
  -- The core is contained in H (instantiate the conjugate at g = ε).
  core-⊆ : proj₁ core ⊆ H
  core-⊆ {x} x∈core = H-respects (conj-action-ε x) (core-mem-conj x∈core ε)

  -- The core is an equality-respecting subgroup: respect holds componentwise
  -- (each conjugate respects ≈ by construction), and the meet of subuniverses
  -- is a subuniverse by the lattice machinery.
  core-isSubgroup : IsSubgroup 𝑮 (proj₁ core)
  core-isSubgroup = record
    { respects       = λ x≈y x∈core i → conjugate-respects (lower i) H x≈y (x∈core i)
    ; isSubuniverse  = proj₂ core
    }

  -- The core is normal: conjugating a member by g keeps every conjugate in H,
  -- since conj k (conj g x) is the (k ∙ g)-conjugate of x.
  core-normal : IsNormal (proj₁ core)
  core-normal g {x} x∈core =
    conj-mem-core (λ k → H-respects (conj-action-∙ k g x) (core-mem-conj x∈core (k ∙ g)))

  -- The core is the greatest normal subgroup contained in H: any normal subset
  -- of H sits inside every conjugate of H, hence inside the meet.
  core-greatest : {ℓⁿ : Level} {N : Pred A ℓⁿ}
    →  IsNormal N → N ⊆ H → N ⊆ proj₁ core
  core-greatest N-normal N⊆H x∈N = conj-mem-core (λ g → N⊆H (N-normal g x∈N))
```
