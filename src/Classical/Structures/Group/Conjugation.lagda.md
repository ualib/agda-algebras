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
open import Data.Fin.Patterns             using  ( 0F ; 1F )
open import Data.Product                  using  ( _,_ ; _×_ ; Σ-syntax ; ∃-syntax
                                                 ; proj₁ ; proj₂ )
open import Function                      using  ( Func )
open import Level                         using  ( Level ; _⊔_ ; lift )
open import Relation.Binary               using  ( Setoid )
open import Relation.Binary.Definitions   using  ( _Respects_ )
open import Relation.Unary                using  ( Pred ; _∈_ ; _⊆_ )

import Algebra.Properties.Group as GroupProperties
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Bundles.Group                           using  ( ⟨_⟩ᵍᵖ )
open import Classical.Signatures.Group                        using  ( Sig-Group ; ∙-Op
                                                                     ; ε-Op ; ⁻¹-Op )
open import Classical.Structures.Group.Basic                  using  ( Group ; module Group-Op )
open import Classical.Structures.Group.Subgroups
open import Setoid.Algebras.Basic            {𝑆 = Sig-Group}  using  ( Algebra ; 𝕌[_] ; 𝔻[_] )
                                                               renaming (_^_ to _̂_ )
open import Setoid.Subalgebras.Subuniverses  {𝑆 = Sig-Group}  using  ( Subuniverses )
open Algebra using (Interp )

open Func renaming ( to to _⟨$⟩_ ; cong to ≈cong )

private variable ℓ ℓ' : Level
```
-->

#### Conjugation of elements

`Conj 𝑮` packages conjugation in the group `𝑮`; opening it puts `conj`{.AgdaFunction}
and its algebra of laws in scope.  The laws say: conjugation by a fixed `g` is a group
endomorphism (`conj-ε`{.AgdaFunction}, `conj-∙-hom`{.AgdaFunction},
`conj-⁻¹`{.AgdaFunction}), and as `g` varies it is a left action of the group on
itself (`conj-action-ε`{.AgdaFunction}, `conj-action-∙`{.AgdaFunction}) by
≈-automorphisms (`conj-cong`{.AgdaFunction}, with `conj-conj⁻¹`{.AgdaFunction} and
`conj⁻¹-conj`{.AgdaFunction} the two inverse laws).

```agda
module Conj {α ρ : Level} (𝒢 : Group α ρ) where
  private
    𝑮 = proj₁ 𝒢
    G = 𝕌[ 𝑮 ]

  open Setoid 𝔻[ 𝑮 ]  using ( _≈_ )
                      renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open SetoidReasoning 𝔻[ 𝑮 ]
  open Group-Op 𝒢 using ( _∙_ ; ε ; _⁻¹ ; ∙-cong ; ⁻¹-cong
                        ; assoc-law ; idˡ-law ; idʳ-law ; invˡ-law ; invʳ-law )
  open GroupProperties ⟨ 𝒢 ⟩ᵍᵖ
    using ( ε⁻¹≈ε ; ⁻¹-involutive ; ⁻¹-anti-homo-∙ ; \\-leftDividesʳ )

  -- Conjugation of the element x by the element g.
  conj : G → G → G
  conj g x = g ∙ x ∙ g ⁻¹

  infixl 30 cong-syntax

  cong-syntax : G → G → G
  cong-syntax = conj

  syntax cong-syntax g x = x ^ g

  -- Conjugation is a congruence in the conjugated element ...
  conj-cong : ∀ g {x y} → x ≈ y → x ^ g ≈ y ^ g
  conj-cong g x≈y = ∙-cong (∙-cong ≈refl x≈y) ≈refl

  -- ... and in the conjugating element.
  conj-congᵍ : ∀ {g h} x → g ≈ h → x ^ g ≈ x ^ h
  conj-congᵍ x g≈h = ∙-cong (∙-cong g≈h ≈refl) (⁻¹-cong g≈h)

  -- Conjugation fixes the identity element.
  conj-ε : ∀ g → ε ^ g  ≈ ε
  conj-ε g = begin
    g ∙ ε ∙ g ⁻¹  ≈⟨ ∙-cong (idʳ-law g) ≈refl ⟩
    g ∙ g ⁻¹      ≈⟨ invʳ-law g ⟩
    ε             ∎

  -- Conjugation by g is multiplicative.
  conj-∙-hom : ∀ g x y → (x ∙ y) ^ g ≈ (x ^ g) ∙ (y ^ g)
  conj-∙-hom g x y = begin
    (x ∙ y) ^ g                        ≈˘⟨ ∙-cong (assoc-law g x y) ≈refl ⟩
    g ∙ x ∙ y ∙ g ⁻¹                   ≈⟨ assoc-law (g ∙ x) y (g ⁻¹) ⟩
    g ∙ x ∙ (y ∙ g ⁻¹)                 ≈˘⟨ ∙-cong ≈refl (\\-leftDividesʳ g (y ∙ g ⁻¹)) ⟩
    g ∙ x ∙ (g ⁻¹ ∙ (g ∙ (y ∙ g ⁻¹)))  ≈˘⟨ ∙-cong ≈refl (∙-cong ≈refl (assoc-law g y (g ⁻¹))) ⟩
    g ∙ x ∙ (g ⁻¹ ∙ (y ^ g))           ≈˘⟨ assoc-law (g ∙ x) (g ⁻¹) (y ^ g) ⟩
    (x ^ g) ∙ (y ^ g)                  ∎

  -- Conjugation by g commutes with inversion.
  conj-⁻¹ : ∀ g x → (x ⁻¹) ^ g ≈ (x ^ g) ⁻¹
  conj-⁻¹ g x = begin
    (x ⁻¹) ^ g              ≈⟨ assoc-law g (x ⁻¹) (g ⁻¹) ⟩
    g ∙ (x ⁻¹ ∙ g ⁻¹)       ≈˘⟨ ∙-cong (⁻¹-involutive g) (⁻¹-anti-homo-∙ g x) ⟩
    (g ⁻¹) ⁻¹ ∙ (g ∙ x) ⁻¹  ≈˘⟨ ⁻¹-anti-homo-∙ (g ∙ x) (g ⁻¹) ⟩
    (x ^ g) ⁻¹ ∎

  -- Varying the conjugator: conjugation is a left action of the group on itself.
  conj-action-∙ : ∀ g h x → x ^ (g ∙ h) ≈ (x ^ h) ^ g
  conj-action-∙ g h x = begin
    x ^ (g ∙ h)                ≈⟨ ≈refl ⟩
    g ∙ h ∙ x ∙ (g ∙ h) ⁻¹     ≈⟨ ∙-cong ≈refl (⁻¹-anti-homo-∙ g h) ⟩
    g ∙ h ∙ x ∙ (h ⁻¹ ∙ g ⁻¹)  ≈˘⟨ assoc-law (g ∙ h ∙ x) (h ⁻¹) (g ⁻¹) ⟩
    g ∙ h ∙ x ∙ h ⁻¹ ∙ g ⁻¹    ≈⟨ ∙-cong (∙-cong (assoc-law g h x) ≈refl) ≈refl ⟩
    g ∙ (h ∙ x) ∙ h ⁻¹ ∙ g ⁻¹  ≈⟨ ∙-cong (assoc-law g (h ∙ x) (h ⁻¹)) ≈refl ⟩
    g ∙ (h ∙ x ∙ h ⁻¹) ∙ g ⁻¹  ≈⟨ ≈refl ⟩
    (x ^ h) ^ g  ∎

  conj-action-ε : ∀ x → x ^ ε ≈ x
  conj-action-ε x = begin
    ε ∙ x ∙ ε ⁻¹  ≈⟨ ∙-cong (idˡ-law x) ε⁻¹≈ε ⟩
    x ∙ ε         ≈⟨ idʳ-law x ⟩
    x             ∎

  -- Conjugating by g undoes conjugating by g ⁻¹, and vice versa.
  conj-conj⁻¹ : ∀ g x → x ^ (g ⁻¹) ^ g ≈ x
  conj-conj⁻¹ g x = begin
    x ^ (g ⁻¹) ^ g    ≈˘⟨ conj-action-∙ g (g ⁻¹) x ⟩
    x ^ (g ∙ g ⁻¹)    ≈⟨ conj-congᵍ x (invʳ-law g) ⟩
    x ^ ε             ≈⟨ conj-action-ε x ⟩
    x                 ∎

  conj⁻¹-conj : ∀ g x → x ^ g ^ (g ⁻¹) ≈ x
  conj⁻¹-conj g x = begin
    x ^ g ^ (g ⁻¹)  ≈˘⟨ conj-action-∙ (g ⁻¹) g x ⟩
    x ^ (g ⁻¹ ∙ g)  ≈⟨ conj-congᵍ x (invˡ-law g) ⟩
    x ^ ε           ≈⟨ conj-action-ε x ⟩
    x               ∎
```

#### Conjugation of subgroups

The conjugate of a subset `B` by `g` is the ≈-saturated image of `B` under
`conj g`{.AgdaFunction}.  It respects the setoid equality by construction, and is a
subuniverse whenever `B` is (via the endomorphism laws above), so conjugation maps
subgroups to subgroups.

```agda
  -- The conjugate subset g B g⁻¹.
  conjugate : G → Pred G ℓ → Pred G (α ⊔ ρ ⊔ ℓ)
  conjugate g B x = ∃[ h ] (h ∈ B × x ≈ h ^ g)

  infixl 30 conjugate-syntax

  conjugate-syntax : G → Pred G ℓ → Pred G (α ⊔ ρ ⊔ ℓ)
  conjugate-syntax = conjugate

  syntax conjugate-syntax g B = [ B ]^ g

  -- The conjugate respects the setoid equality, with no hypothesis on B.
  conjugate-respects : ∀ g (B : Pred G ℓ) → [ B ]^ g Respects _≈_
  conjugate-respects g B x≈y (h , h∈B , x≈c) = h , h∈B , ≈trans (≈sym x≈y) x≈c

  -- Conjugation of an element lands in the conjugate of any subset containing it.
  mem-conjugate : ∀ g {B : Pred G ℓ} {x} → x ∈ B → x ^ g ∈ [ B ]^ g
  mem-conjugate g x∈B = _ , x∈B , ≈refl

  -- Conjugation of subsets is monotone.
  conjugate-mono : ∀ g {B : Pred G ℓ} {C : Pred G ℓ'} → B ⊆ C → [ B ]^ g ⊆ [ C ]^ g
  conjugate-mono g B⊆C (h , h∈B , x≈c) = h , B⊆C h∈B , x≈c

  -- The conjugate of a subuniverse is a subuniverse.
  conjugate-isSubuniverse : (g : G) (B : Pred G ℓ)
    →  B ∈ Subuniverses 𝑮 → [ B ]^ g ∈ Subuniverses 𝑮
  conjugate-isSubuniverse g B B-sub ∙-Op a im =
    h₀ ∙ h₁ , sub-∙-closed 𝒢 B B-sub h₀∈B h₁∈B , eq
    where
    h₀ h₁ : G
    h₀ = im 0F .proj₁
    h₁ = im 1F .proj₁

    h₀∈B : h₀ ∈ B
    h₀∈B = im 0F .proj₂ .proj₁

    h₁∈B : h₁ ∈ B
    h₁∈B = im 1F .proj₂ .proj₁

    eq : (∙-Op ̂  𝑮) a ≈ (h₀ ∙ h₁) ^ g
    eq = begin
      (∙-Op ̂  𝑮) a      ≈⟨ interp-tuple-∙ 𝒢 a ⟩
      a 0F ∙ a 1F       ≈⟨ ∙-cong (im 0F .proj₂ .proj₂) (im 1F .proj₂ .proj₂) ⟩
      h₀ ^ g ∙ h₁ ^ g   ≈˘⟨ conj-∙-hom g h₀ h₁ ⟩
      (h₀ ∙ h₁) ^ g     ∎

  conjugate-isSubuniverse g B B-sub ε-Op a im = ε , sub-ε-closed 𝒢 B B-sub , eq
    where
    eq : (ε-Op ̂  𝑮) a ≈ ε ^ g
    eq = begin
      (ε-Op ̂  𝑮) a  ≈⟨ interp-tuple-ε 𝒢 a ⟩
      ε             ≈˘⟨ conj-ε g ⟩
      ε ^ g         ∎

  conjugate-isSubuniverse g B B-sub ⁻¹-Op a im = h ⁻¹ , sub-⁻¹-closed 𝒢 B B-sub h∈B , eq
    where
    h : G
    h = im 0F .proj₁

    h∈B : h ∈ B
    h∈B = im 0F .proj₂ .proj₁

    eq : (⁻¹-Op ̂  𝑮) a ≈ (h ⁻¹) ^ g
    eq = begin
      (⁻¹-Op ̂  𝑮) a  ≈⟨ interp-tuple-⁻¹ 𝒢 a ⟩
      a 0F ⁻¹        ≈⟨ ⁻¹-cong (im 0F .proj₂ .proj₂) ⟩
      (h ^ g) ⁻¹     ≈˘⟨ conj-⁻¹ g h ⟩
      (h ⁻¹) ^ g     ∎
```

#### The normality predicate

A subset is **normal** when it is closed under conjugation by every group element.
The property is stated for bare predicates; for ≈-respecting subgroups it is
equivalent to each conjugate coinciding with the subgroup, and the three bridge
lemmas make both directions available in the form each client needs.

```agda
  -- The normality predicate: closure under conjugation, pointwise.
  IsNormal : Pred G ℓ → Type (α ⊔ ℓ)
  IsNormal B = ∀ g {x} → x ∈ B → x ^ g ∈ B

  -- For a respecting subset, normality bounds every conjugate above by B ...
  normal-conjugate-⊆ : {B : Pred G ℓ}
    →  B Respects _≈_ → IsNormal B → ∀ g → [ B ]^ g ⊆ B
  normal-conjugate-⊆ resp nrmB g (h , h∈B , x≈c) = resp (≈sym x≈c) (nrmB g h∈B)

  -- ... and below by B (this direction needs no respect hypothesis) ...
  normal-⊆-conjugate : {B : Pred G ℓ} → IsNormal B → ∀ g → B ⊆ [ B ]^ g
  normal-⊆-conjugate nrmB g {x} x∈B = x ^ (g ⁻¹) , nrmB (g ⁻¹) x∈B , ≈sym (conj-conj⁻¹ g x)

  -- ... and conversely, a subset above all of its conjugates is normal.
  conjugate-⊆-normal : {B : Pred G ℓ} → (∀ g → [ B ]^ g ⊆ B) → IsNormal B
  conjugate-⊆-normal cnj g x∈B = cnj g (mem-conjugate g x∈B)

  -- The trivial subgroup and the full subgroup are normal.
  trivialSubgroupIsnormal : IsNormal (trivialSubgroup 𝒢 .proj₁)
  trivialSubgroupIsnormal g x≈ε = ≈trans (conj-cong g x≈ε) (conj-ε g)

  fullSubgroupIsnormal : (ℓ : Level) → IsNormal (proj₁ (fullSubgroup 𝒢 ℓ))
  fullSubgroupIsnormal ℓ _ _ = lift _
```
