---
layout: default
file: "src/Classical/Structures/Group/Subgroups.lagda.md"
title: "Classical.Structures.Group.Subgroups module"
date: "2026-07-11"
author: "the agda-algebras development team"
---

### Subgroups of an arbitrary group

This is the [Classical.Structures.Group.Subgroups][] module of the [Agda Universal Algebra Library][].

For a group `𝑮`{.AgdaBound} presented as a Σ-typed structure over
[`Sig-Group`][Classical.Signatures.Group] (per [Classical.Structures.Group][]), a
**subgroup** is a subset of the carrier that is closed under the three basic
operations — that is, a *subuniverse* of the underlying algebra in the sense of
[Setoid.Subalgebras.Subuniverses][].  This module generalizes the concrete treatment
of the Klein four-group in [Examples.Setoid.SubgroupLattice][] to an arbitrary group.

Because the carrier of a setoid algebra comes with a setoid equality `_≈_`{.AgdaFunction},
a subset that is to play the role of a subgroup in *theorems* (conjugation, cosets,
Dedekind's rule) must also be compatible with that equality.  We therefore package a
subgroup predicate as a record `IsSubgroup`{.AgdaRecord} with two fields:

+  `respects`{.AgdaField} — the predicate respects the setoid equality (`B Respects _≈_`);
+  `isSubuniverse`{.AgdaField} — the predicate is closed under the interpreted operations.

The first field is invisible in the classical (`_≡_`-setoid) case — where it holds by
`subst`{.AgdaFunction} — and is exactly what setoid-based group theory needs; the second
field alone already suffices to place the subgroup in the subuniverse lattice of
[Setoid.Subalgebras.CompleteLattice][] (see [Classical.Structures.Group.SubgroupLattice][]).

The module also provides the *curried closure toolkit*: a subuniverse of a group
algebra is closed under the curried `_∙_`{.AgdaFunction}, contains `ε`{.AgdaFunction},
and is closed under `_⁻¹`{.AgdaFunction}; and conversely those three closure properties
(together with `respects`{.AgdaField}) make a predicate a subgroup
(`mkIsSubgroup`{.AgdaFunction}).  The trivial subgroup `{ x ∣ x ≈ ε }` and the full
subgroup close the module.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.Subgroups where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base                 using ( Fin )
open import Data.Fin.Patterns             using ( 0F ; 1F )
open import Data.Product                  using ( _,_ ; Σ-syntax ; proj₁ )
open import Data.Unit.Base                using ( ⊤ ; tt )
open import Level                         using ( Level ; _⊔_ ; suc ; Lift ; lift )
open import Relation.Binary               using ( Setoid )
open import Relation.Binary.Definitions   using ( _Respects_ )
open import Relation.Unary                using ( Pred ; _∈_ )

import Algebra.Properties.Group as GroupProperties

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Bundles.Group           using ( ⟨_⟩ᵍᵖ )
open import Classical.Operations              using ( pair )
open import Classical.Signatures.Group        using ( ∙-Op ; ε-Op ; ⁻¹-Op )
open import Classical.Structures.Group.Basic  using ( Group ; module Group-Op )
open import Classical.Structures.Interpret    using ( interp-cong )
open import Setoid.Algebras.Basic             using ( Algebra ; 𝕌[_] ; 𝔻[_] ; _^_ )
open import Setoid.Subalgebras.Subuniverses   using ( Subuniverses )

private variable α ρ ℓ : Level
```
-->

#### Tuple-vs-curried interpretation bridges

The subuniverse machinery speaks of tuple-indexed operations `(f ^ 𝑨) a`, while
group theory speaks of the curried `x ∙ y`, `ε`, `x ⁻¹` of `Group-Op`{.AgdaModule}.
The two agree up to the setoid equality: `(f ^ 𝑨) a` applied to an arbitrary tuple
`a` equals the curried operation applied to the components of `a`, by congruence of
the interpretation (`interp-cong`{.AgdaFunction}).  These three bridges are the only
place the mismatch is handled; everything downstream uses them.

```agda
module _ (𝑮 : Group α ρ) where
  private
    𝑨 = proj₁ 𝑮
    A = 𝕌[ 𝑨 ]

  open Setoid 𝔻[ 𝑨 ]  using ( _≈_ )
                      renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open Group-Op 𝑮     using ( _∙_ ; ε ; _⁻¹ ; ∙-cong ; ⁻¹-cong ; idˡ-law )
  open GroupProperties ⟨ 𝑮 ⟩ᵍᵖ using ( ε⁻¹≈ε )

  -- The binary operation on an arbitrary 2-tuple is the curried ∙ of its components.
  interp-tuple-∙ : (a : Fin 2 → A) → (∙-Op ^ 𝑨) a ≈ a 0F ∙ a 1F
  interp-tuple-∙ a = interp-cong 𝑨 ∙-Op (λ { 0F → ≈refl ; 1F → ≈refl })

  -- The nullary operation on an arbitrary 0-tuple is the identity element ε.
  interp-tuple-ε : (a : Fin 0 → A) → (ε-Op ^ 𝑨) a ≈ ε
  interp-tuple-ε a = interp-cong 𝑨 ε-Op (λ ())

  -- The unary operation on an arbitrary 1-tuple is the curried ⁻¹ of its component.
  interp-tuple-⁻¹ : (a : Fin 1 → A) → (⁻¹-Op ^ 𝑨) a ≈ a 0F ⁻¹
  interp-tuple-⁻¹ a = interp-cong 𝑨 ⁻¹-Op (λ { 0F → ≈refl })
```

#### The curried closure toolkit

A subuniverse of the group algebra is closed under each curried operation.  These are
definitional consequences of closure under the tuple-indexed operations, because the
curried accessors of `Group-Op`{.AgdaModule} are defined by applying the interpreted
symbol to a canonical tuple.

```agda
  module _ (B : Pred A ℓ) (B-sub : B ∈ Subuniverses 𝑨) where
    -- A subuniverse is closed under the curried group multiplication.
    sub-∙-closed : ∀ {x y} → x ∈ B → y ∈ B → x ∙ y ∈ B
    sub-∙-closed {x} {y} x∈B y∈B = B-sub ∙-Op (pair x y) im
      where
      im : (i : Fin 2) → pair x y i ∈ B
      im 0F = x∈B
      im 1F = y∈B

    -- A subuniverse contains the identity element (the nullary operation forces it).
    sub-ε-closed : ε ∈ B
    sub-ε-closed = B-sub ε-Op (λ ()) (λ ())

    -- A subuniverse is closed under the curried inverse.
    sub-⁻¹-closed : ∀ {x} → x ∈ B → x ⁻¹ ∈ B
    sub-⁻¹-closed {x} x∈B = B-sub ⁻¹-Op (λ _ → x) (λ _ → x∈B)
```

#### The subgroup predicate

`IsSubgroup B` says the predicate `B` cuts out a subgroup: it respects the setoid
equality and is a subuniverse of the group algebra.  The record module re-exports the
curried closure properties, so `open IsSubgroup H-isSubgroup` puts
`∙-closed`{.AgdaFunction}, `ε-closed`{.AgdaFunction}, `⁻¹-closed`{.AgdaFunction}, and
`respects`{.AgdaField} in scope for a fixed subgroup.

```agda
  record IsSubgroup (B : Pred A ℓ) : Type (α ⊔ ρ ⊔ ℓ) where
    field
      respects       : B Respects _≈_
      isSubuniverse  : B ∈ Subuniverses 𝑨

    ∙-closed : ∀ {x y} → x ∈ B → y ∈ B → x ∙ y ∈ B
    ∙-closed = sub-∙-closed B isSubuniverse

    ε-closed : ε ∈ B
    ε-closed = sub-ε-closed B isSubuniverse

    ⁻¹-closed : ∀ {x} → x ∈ B → x ⁻¹ ∈ B
    ⁻¹-closed = sub-⁻¹-closed B isSubuniverse
```

Conversely, an equality-respecting predicate that is closed under the three curried
operations is a subgroup: the tuple-indexed closure required by
`Subuniverses`{.AgdaFunction} follows from the curried closure by rewriting along the
interpretation bridges (this is the one direction that genuinely *uses*
`respects`{.AgdaField}).

```agda
  mkIsSubgroup : {B : Pred A ℓ}
    →  B Respects _≈_
    →  (∀ {x y} → x ∈ B → y ∈ B → x ∙ y ∈ B)
    →  ε ∈ B
    →  (∀ {x} → x ∈ B → x ⁻¹ ∈ B)
    →  IsSubgroup B
  mkIsSubgroup {B = B} resp ∙-c ε-c ⁻¹-c = record { respects = resp ; isSubuniverse = isSub }
    where
    isSub : B ∈ Subuniverses 𝑨
    isSub ∙-Op   a im = resp (≈sym (interp-tuple-∙ a)) (∙-c (im 0F) (im 1F))
    isSub ε-Op   a im = resp (≈sym (interp-tuple-ε a)) ε-c
    isSub ⁻¹-Op  a im = resp (≈sym (interp-tuple-⁻¹ a)) (⁻¹-c (im 0F))
```

#### The type of subgroups

A subgroup of `𝑮` at predicate level `ℓ` is a predicate on the carrier together with
a proof that it is a subgroup.

```agda
  Subgroup : (ℓ : Level) → Type (α ⊔ ρ ⊔ suc ℓ)
  Subgroup ℓ = Σ[ B ∈ Pred A ℓ ] IsSubgroup B
```

#### The trivial and full subgroups

The trivial subgroup is the ≈-class of the identity, `{ x ∣ x ≈ ε }` — over a setoid
carrier the *class*, not the syntactic singleton, is the right notion.  The full
subgroup is the whole carrier.

```agda
  trivialSubgroup : Subgroup ρ
  trivialSubgroup = (λ x → x ≈ ε) , mkIsSubgroup resp ∙-c ε-c ⁻¹-c
    where
    resp : (λ x → x ≈ ε) Respects _≈_
    resp x≈y x≈ε = ≈trans (≈sym x≈y) x≈ε

    ∙-c : ∀ {x y} → x ≈ ε → y ≈ ε → x ∙ y ≈ ε
    ∙-c x≈ε y≈ε = ≈trans (∙-cong x≈ε y≈ε) (idˡ-law ε)

    ε-c : ε ≈ ε
    ε-c = ≈refl

    ⁻¹-c : ∀ {x} → x ≈ ε → x ⁻¹ ≈ ε
    ⁻¹-c x≈ε = ≈trans (⁻¹-cong x≈ε) ε⁻¹≈ε

  fullSubgroup : (ℓ : Level) → Subgroup ℓ
  fullSubgroup ℓ =  (λ _ → Lift ℓ ⊤)
                 ,  mkIsSubgroup (λ _ _ → lift tt) (λ _ _ → lift tt) (lift tt) (λ _ → lift tt)
```
