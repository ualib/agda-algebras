---
layout: default
file: "src/Classical/Structures/Group/Conjugation.lagda.md"
title: "Classical.Structures.Group.Conjugation module"
date: "2026-07-11"
author: "the agda-algebras development team"
---

### Conjugation and normality

This is the [Classical.Structures.Group.Conjugation][] module of the [Agda Universal Algebra Library][].

For a group `𝑮`{.AgdaBound} this module develops conjugation — first of elements
(`conj g x = g ∙ x ∙ g ⁻¹`), then of subgroups — and the normality predicate, the
ingredients from which [Classical.Structures.Group.NormalCore][] builds the normal
core `Core_G(H)` as a complete-lattice meet.

Two design points deserve comment.

+  **The conjugate of a subgroup is defined as an image, not a preimage**.  We take
   `conjugate g B = { x ∣ ∃ h ∈ B , x ≈ conj g h }`, the ≈-saturated image of `B`
   under `conj g`, rather than the preimage `{ x ∣ conj (g ⁻¹) x ∈ B }`.  Over a
   setoid carrier the image form is superior: it respects the setoid equality *by
   construction* (no hypothesis on `B` needed), and it is a subuniverse whenever `B`
   is a bare subuniverse.  For equality-respecting `B` the two forms agree.
+  **Normality is the pointwise property** `∀ g x → x ∈ B → conj g x ∈ B`.  The
   bridge lemmas `normal-conjugate-⊆`{.AgdaFunction} and
   `normal-⊆-conjugate`{.AgdaFunction} recover the equivalent formulation "every
   conjugate of `B` coincides with `B`" when `B` respects the equality.

All proofs are small equational chains over the group axioms; the derived
cancellation laws (`\\-leftDividesʳ` and friends) come from the standard library's
`Algebra.Properties.Group`{.AgdaModule} applied to the bundle view
`⟨ 𝑮 ⟩ᵍᵖ`{.AgdaFunction} of [Classical.Bundles.Group][], which is what the bundle
bridge exists for.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.Conjugation where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Patterns             using ( 0F ; 1F )
open import Data.Product                  using ( _,_ ; _×_ ; Σ-syntax ; proj₁ ; proj₂ )
open import Level                         using ( Level ; _⊔_ ; lift )
open import Relation.Binary               using ( Setoid )
open import Relation.Binary.Definitions   using ( _Respects_ )
open import Relation.Unary                using ( Pred ; _∈_ ; _⊆_ )

import Algebra.Properties.Group as GroupProperties
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Bundles.Group          using ( ⟨_⟩ᵍᵖ )
open import Classical.Signatures.Group       using ( Sig-Group ; ∙-Op ; ε-Op ; ⁻¹-Op )
open import Classical.Structures.Group       using ( Group ; module Group-Op )
open import Classical.Structures.Group.Subgroups
  using ( sub-∙-closed ; sub-ε-closed ; sub-⁻¹-closed
        ; interp-tuple-∙ ; interp-tuple-ε ; interp-tuple-⁻¹
        ; trivialSubgroup ; fullSubgroup )

open import Setoid.Algebras.Basic {𝑆 = Sig-Group}           using ( Algebra ; 𝕌[_] ; 𝔻[_] ; _^_ )
open import Setoid.Subalgebras.Subuniverses {𝑆 = Sig-Group} using ( Subuniverses )

private variable ℓ ℓ' : Level
```
-->

#### Conjugation of elements

`Conj 𝑮` packages conjugation in the group `𝑮`; opening it puts `conj`{.AgdaFunction}
and its algebra of laws in scope.  The laws say: conjugation by a fixed `g` is a group
endomorphism (`conj-ε`{.AgdaFunction}, `conj-homo-∙`{.AgdaFunction},
`conj-⁻¹`{.AgdaFunction}), and as `g` varies it is a left action of the group on
itself (`conj-action-ε`{.AgdaFunction}, `conj-action-∙`{.AgdaFunction}) by
≈-automorphisms (`conj-cong`{.AgdaFunction}, with `conj-conj⁻¹`{.AgdaFunction} and
`conj⁻¹-conj`{.AgdaFunction} the two inverse laws).

```agda
module Conj {α ρ : Level} (𝑮 : Group α ρ) where
  private
    𝑨 = proj₁ 𝑮
    A = 𝕌[ 𝑨 ]

  open Setoid 𝔻[ 𝑨 ]  using ( _≈_ )
                      renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open SetoidReasoning 𝔻[ 𝑨 ]
  open Group-Op 𝑮 using ( _∙_ ; ε ; _⁻¹ ; ∙-cong ; ⁻¹-cong
                        ; assoc-law ; idˡ-law ; idʳ-law ; invˡ-law ; invʳ-law )
  open GroupProperties (⟨ 𝑮 ⟩ᵍᵖ)
    using ( ε⁻¹≈ε ; ⁻¹-involutive ; ⁻¹-anti-homo-∙ ; \\-leftDividesʳ )

  -- Conjugation of the element x by the element g.
  conj : A → A → A
  conj g x = g ∙ x ∙ g ⁻¹

  -- Conjugation is a congruence in the conjugated element ...
  conj-cong : ∀ g {x y} → x ≈ y → conj g x ≈ conj g y
  conj-cong g x≈y = ∙-cong (∙-cong ≈refl x≈y) ≈refl

  -- ... and in the conjugating element.
  conj-congᵍ : ∀ {g h} x → g ≈ h → conj g x ≈ conj h x
  conj-congᵍ x g≈h = ∙-cong (∙-cong g≈h ≈refl) (⁻¹-cong g≈h)

  -- Conjugation fixes the identity element.
  conj-ε : ∀ g → conj g ε ≈ ε
  conj-ε g = begin
    g ∙ ε ∙ g ⁻¹  ≈⟨ ∙-cong (idʳ-law g) ≈refl ⟩
    g ∙ g ⁻¹      ≈⟨ invʳ-law g ⟩
    ε             ∎

  -- Conjugation by g is multiplicative.
  conj-homo-∙ : ∀ g x y → conj g (x ∙ y) ≈ conj g x ∙ conj g y
  conj-homo-∙ g x y = ≈sym (begin
    (g ∙ x ∙ g ⁻¹) ∙ (g ∙ y ∙ g ⁻¹)      ≈⟨ assoc-law (g ∙ x) (g ⁻¹) (g ∙ y ∙ g ⁻¹) ⟩
    g ∙ x ∙ (g ⁻¹ ∙ (g ∙ y ∙ g ⁻¹))      ≈⟨ ∙-cong ≈refl (∙-cong ≈refl (assoc-law g y (g ⁻¹))) ⟩
    g ∙ x ∙ (g ⁻¹ ∙ (g ∙ (y ∙ g ⁻¹)))    ≈⟨ ∙-cong ≈refl (\\-leftDividesʳ g (y ∙ g ⁻¹)) ⟩
    g ∙ x ∙ (y ∙ g ⁻¹)                   ≈˘⟨ assoc-law (g ∙ x) y (g ⁻¹) ⟩
    g ∙ x ∙ y ∙ g ⁻¹                     ≈⟨ ∙-cong (assoc-law g x y) ≈refl ⟩
    g ∙ (x ∙ y) ∙ g ⁻¹                   ∎)

  -- Conjugation by g commutes with inversion.
  conj-⁻¹ : ∀ g x → conj g (x ⁻¹) ≈ (conj g x) ⁻¹
  conj-⁻¹ g x = ≈sym (begin
    (g ∙ x ∙ g ⁻¹) ⁻¹          ≈⟨ ⁻¹-anti-homo-∙ (g ∙ x) (g ⁻¹) ⟩
    (g ⁻¹) ⁻¹ ∙ (g ∙ x) ⁻¹     ≈⟨ ∙-cong (⁻¹-involutive g) (⁻¹-anti-homo-∙ g x) ⟩
    g ∙ (x ⁻¹ ∙ g ⁻¹)          ≈˘⟨ assoc-law g (x ⁻¹) (g ⁻¹) ⟩
    g ∙ x ⁻¹ ∙ g ⁻¹            ∎)

  -- Varying the conjugator: conjugation is a left action of the group on itself.
  conj-action-∙ : ∀ g h x → conj (g ∙ h) x ≈ conj g (conj h x)
  conj-action-∙ g h x = begin
    g ∙ h ∙ x ∙ (g ∙ h) ⁻¹        ≈⟨ ∙-cong ≈refl (⁻¹-anti-homo-∙ g h) ⟩
    g ∙ h ∙ x ∙ (h ⁻¹ ∙ g ⁻¹)     ≈˘⟨ assoc-law (g ∙ h ∙ x) (h ⁻¹) (g ⁻¹) ⟩
    g ∙ h ∙ x ∙ h ⁻¹ ∙ g ⁻¹       ≈⟨ ∙-cong (∙-cong (assoc-law g h x) ≈refl) ≈refl ⟩
    g ∙ (h ∙ x) ∙ h ⁻¹ ∙ g ⁻¹     ≈⟨ ∙-cong (assoc-law g (h ∙ x) (h ⁻¹)) ≈refl ⟩
    g ∙ (h ∙ x ∙ h ⁻¹) ∙ g ⁻¹     ∎

  conj-action-ε : ∀ x → conj ε x ≈ x
  conj-action-ε x = begin
    ε ∙ x ∙ ε ⁻¹  ≈⟨ ∙-cong (idˡ-law x) ε⁻¹≈ε ⟩
    x ∙ ε         ≈⟨ idʳ-law x ⟩
    x             ∎

  -- Conjugating by g undoes conjugating by g ⁻¹, and vice versa.
  conj-conj⁻¹ : ∀ g x → conj g (conj (g ⁻¹) x) ≈ x
  conj-conj⁻¹ g x = begin
    conj g (conj (g ⁻¹) x)  ≈˘⟨ conj-action-∙ g (g ⁻¹) x ⟩
    conj (g ∙ g ⁻¹) x       ≈⟨ conj-congᵍ x (invʳ-law g) ⟩
    conj ε x                ≈⟨ conj-action-ε x ⟩
    x                       ∎

  conj⁻¹-conj : ∀ g x → conj (g ⁻¹) (conj g x) ≈ x
  conj⁻¹-conj g x = begin
    conj (g ⁻¹) (conj g x)  ≈˘⟨ conj-action-∙ (g ⁻¹) g x ⟩
    conj (g ⁻¹ ∙ g) x       ≈⟨ conj-congᵍ x (invˡ-law g) ⟩
    conj ε x                ≈⟨ conj-action-ε x ⟩
    x                       ∎
```

#### Conjugation of subgroups

The conjugate of a subset `B` by `g` is the ≈-saturated image of `B` under
`conj g`{.AgdaFunction}.  It respects the setoid equality by construction, and is a
subuniverse whenever `B` is (via the endomorphism laws above), so conjugation maps
subgroups to subgroups.

```agda
  -- The conjugate subset g B g⁻¹.
  conjugate : A → Pred A ℓ → Pred A (α ⊔ ρ ⊔ ℓ)
  conjugate g B x = Σ[ h ∈ A ] (h ∈ B × x ≈ conj g h)

  -- The conjugate respects the setoid equality, with no hypothesis on B.
  conjugate-respects : ∀ g (B : Pred A ℓ) → conjugate g B Respects _≈_
  conjugate-respects g B x≈y (h , h∈B , x≈c) = h , h∈B , ≈trans (≈sym x≈y) x≈c

  -- Conjugation of an element lands in the conjugate of any subset containing it.
  mem-conjugate : ∀ g {B : Pred A ℓ} {x} → x ∈ B → conj g x ∈ conjugate g B
  mem-conjugate g x∈B = _ , x∈B , ≈refl

  -- Conjugation of subsets is monotone.
  conjugate-mono : ∀ g {B : Pred A ℓ} {C : Pred A ℓ'} → B ⊆ C → conjugate g B ⊆ conjugate g C
  conjugate-mono g B⊆C (h , h∈B , x≈c) = h , B⊆C h∈B , x≈c

  -- The conjugate of a subuniverse is a subuniverse.
  conjugate-isSubuniverse : ∀ g {B : Pred A ℓ}
    →  B ∈ Subuniverses 𝑨 → conjugate g B ∈ Subuniverses 𝑨
  conjugate-isSubuniverse g {B} B-sub ∙-Op a im =
    h₀ ∙ h₁ , sub-∙-closed 𝑮 {B = B} B-sub (proj₁ (proj₂ (im 0F))) (proj₁ (proj₂ (im 1F))) , eq
    where
    h₀ h₁ : A
    h₀ = proj₁ (im 0F)
    h₁ = proj₁ (im 1F)

    eq : (∙-Op ^ 𝑨) a ≈ conj g (h₀ ∙ h₁)
    eq = begin
      (∙-Op ^ 𝑨) a           ≈⟨ interp-tuple-∙ 𝑮 a ⟩
      a 0F ∙ a 1F            ≈⟨ ∙-cong (proj₂ (proj₂ (im 0F))) (proj₂ (proj₂ (im 1F))) ⟩
      conj g h₀ ∙ conj g h₁  ≈˘⟨ conj-homo-∙ g h₀ h₁ ⟩
      conj g (h₀ ∙ h₁)       ∎

  conjugate-isSubuniverse g {B} B-sub ε-Op a im =
    ε , sub-ε-closed 𝑮 {B = B} B-sub , ≈trans (interp-tuple-ε 𝑮 a) (≈sym (conj-ε g))

  conjugate-isSubuniverse g {B} B-sub ⁻¹-Op a im =
    h ⁻¹ , sub-⁻¹-closed 𝑮 {B = B} B-sub (proj₁ (proj₂ (im 0F))) , eq
    where
    h : A
    h = proj₁ (im 0F)

    eq : (⁻¹-Op ^ 𝑨) a ≈ conj g (h ⁻¹)
    eq = begin
      (⁻¹-Op ^ 𝑨) a  ≈⟨ interp-tuple-⁻¹ 𝑮 a ⟩
      a 0F ⁻¹        ≈⟨ ⁻¹-cong (proj₂ (proj₂ (im 0F))) ⟩
      (conj g h) ⁻¹  ≈˘⟨ conj-⁻¹ g h ⟩
      conj g (h ⁻¹)  ∎
```

#### The normality predicate

A subset is **normal** when it is closed under conjugation by every group element.
The property is stated for bare predicates; for equality-respecting subgroups it is
equivalent to each conjugate coinciding with the subgroup, and the three bridge
lemmas make both directions available in the form each client needs.

```agda
  -- The normality predicate: closure under conjugation, pointwise.
  IsNormal : Pred A ℓ → Type (α ⊔ ℓ)
  IsNormal B = ∀ g {x} → x ∈ B → conj g x ∈ B

  -- For a respecting subset, normality bounds every conjugate above by B ...
  normal-conjugate-⊆ : {B : Pred A ℓ}
    →  B Respects _≈_ → IsNormal B → ∀ g → conjugate g B ⊆ B
  normal-conjugate-⊆ resp nrmB g (h , h∈B , x≈c) = resp (≈sym x≈c) (nrmB g h∈B)

  -- ... and below by B (this direction needs no respect hypothesis) ...
  normal-⊆-conjugate : {B : Pred A ℓ} → IsNormal B → ∀ g → B ⊆ conjugate g B
  normal-⊆-conjugate nrmB g {x} x∈B = conj (g ⁻¹) x , nrmB (g ⁻¹) x∈B , ≈sym (conj-conj⁻¹ g x)

  -- ... and conversely, a subset above all of its conjugates is normal.
  conjugate-⊆-normal : {B : Pred A ℓ} → (∀ g → conjugate g B ⊆ B) → IsNormal B
  conjugate-⊆-normal cnj g x∈B = cnj g (mem-conjugate g x∈B)

  -- The trivial subgroup and the full subgroup are normal.
  trivialSubgroup-normal : IsNormal (proj₁ (trivialSubgroup 𝑮))
  trivialSubgroup-normal g x≈ε = ≈trans (conj-cong g x≈ε) (conj-ε g)

  fullSubgroup-normal : (ℓ : Level) → IsNormal (proj₁ (fullSubgroup 𝑮 ℓ))
  fullSubgroup-normal ℓ _ _ = lift _
```
