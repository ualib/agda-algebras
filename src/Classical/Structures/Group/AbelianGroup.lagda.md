---
layout: default
file: "src/Classical/Structures/Group/AbelianGroup.lagda.md"
title: "Classical.Structures.Group.AbelianGroup module"
date: "2026-05-30"
author: "the agda-algebras development team"
---

### Abelian Groups {#classical-structures-abeliangroup}

This is the [Classical.Structures.Group.AbelianGroup][] module of the [Agda Universal Algebra Library][].

An **abelian group** is an inhabitant of the type
`Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ Th-AbelianGroup`, where `Algebra` is parameterized by
the signature type `Sig-Group`.

This is an equation-only extension of Group, structurally identical to the way
`CommutativeMonoid` extends `Monoid`; that is, `abelianGroup→group` is a pure
theory-reindex (`proj₁` on the underlying algebra), and `AbelianGroup-Op` inherits
`_∙_`, `ε`, `_⁻¹`, and all five group laws through it, adding `comm-law`.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.AbelianGroup where

open import Agda.Primitive                         using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Level                                  using ( Level ; _⊔_ ; suc )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( _≡_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Signatures.Group             using ( Sig-Group )
open import Classical.Structures.Group.Basic       using ( Group ; module Group-Op ; opsToBareGroup )
open import Classical.Theories.Group               using ( assoc ; idˡ ; idʳ ; invˡ ; invʳ )
open import Classical.Theories.AbelianGroup        using ( Eq-AbelianGroup ; Th-AbelianGroup ; comm )
                                                   renaming ( assoc to assocᵃ ; idˡ to idˡᵃ ; idʳ to idʳᵃ
                                                            ; invˡ to invˡᵃ ; invʳ to invʳᵃ )
open import Overture.Terms                         using ( Term ; ℊ )
open import Setoid.Algebras.Basic                  using ( Algebra ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Varieties.EquationalLogic using ( _⊧_≈_ )

private variable α ρ : Level
```
-->

#### Satisfaction predicate and the `AbelianGroup` type

```agda
infix 4 _⊨ᵃᵍ_
_⊨ᵃᵍ_ : (𝑨 : Algebra {𝑆 = Sig-Group} α ρ) (ℰ : Eq-AbelianGroup → Term (Fin 3) × Term (Fin 3)) → Type (α ⊔ ρ)
𝑨 ⊨ᵃᵍ ℰ = ∀ i → 𝑨 ⊧ proj₁ (ℰ i) ≈ proj₂ (ℰ i)

AbelianGroup : (α ρ : Level) → Type (suc α ⊔ suc ρ)
AbelianGroup α ρ = Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ᵃᵍ Th-AbelianGroup
```

#### The forgetful projection to groups

`abelianGroup→group`{.AgdaFunction} discards commutativity.  Since an abelian
group is a group with one extra *equation* and no extra operations, the signature
is unchanged and no reduct is needed; the function keeps the algebra and re-indexes
the satisfaction witness, mapping each constructor of `Eq-Group`{.AgdaDatatype} to
its counterpart in `Eq-AbelianGroup`{.AgdaDatatype}.  (This is the shape forgetful
shape as that of `commutativeMonoid→monoid`{.AgdaFunction}, in contrast with the
reduct-and-re-prove shape of `monoid→semigroup`{.AgdaFunction}.)

```agda
abelianGroup→group : AbelianGroup α ρ → Group α ρ
abelianGroup→group (𝑨 , mod) = 𝑨 , λ  { assoc → mod assocᵃ
                                      ; idˡ   → mod idˡᵃ
                                      ; idʳ   → mod idʳᵃ
                                      ; invˡ  → mod invˡᵃ
                                      ; invʳ  → mod invʳᵃ }
```

#### The `AbelianGroup-Op` module

`AbelianGroup-Op`{.AgdaModule}` 𝑨` inherits the whole group interface through the
forgetful projection (three operations, both congruences, all three containment
lemmas and all five laws) and adds two names: `equations`{.AgdaFunction}, the new
satisfaction witness, and `comm-law`{.AgdaFunction}, commutativity in curried form.

```agda
module AbelianGroup-Op {α ρ : Level} ((𝑨 , laws) : AbelianGroup α ρ) where
  open Setoid 𝔻[ 𝑨 ]

  open Group-Op (abelianGroup→group (𝑨 , laws)) public
    using  ( _∙_ ; ε ; _⁻¹ ; ∙-cong ; ⁻¹-cong ; interp-node-∙ ; interp-node-ε
           ; interp-node-⁻¹ ; assoc-law ; idˡ-law ; idʳ-law ; invˡ-law ; invʳ-law )

  comm-law : ∀ x y → x ∙ y ≈ y ∙ x
  comm-law x y = trans (sym (interp-node-∙ (ℊ 0F) (ℊ 1F) {η}))
                       (trans (laws comm η) (interp-node-∙ (ℊ 1F) (ℊ 0F) {η}))
               -- the same three-step shape every added law in the hierarchy has:
               -- `laws comm` between two applications of `interp-node-∙`, one
               -- for each side of the equation.
    where
    η : Fin 3 → 𝕌[ 𝑨 ]
    η = λ { 0F → x ; 1F → y ; 2F → x }
```

#### `eqsToAbelianGroup`

`eqsToAbelianGroup`{.AgdaFunction} is the constructor a downstream user calls: a
carrier, a binary operation, an identity, an inverse, and the six laws as
*propositional* equations.  Every obligation discharges by definitional reduction,
since under `≡.setoid A` the setoid equality is propositional equality and each
interpreted term reduces to the corresponding application of the supplied
operations.

```agda
eqsToAbelianGroup : {A : Type α} (_·_ : A → A → A) (e : A) (i : A → A)
  → (·-assoc : ∀ a b c → (a · b) · c ≡ a · (b · c))
  → (·-idˡ : ∀ a → e · a ≡ a) (·-idʳ : ∀ a → a · e ≡ a)
  → (·-invˡ : ∀ a → (i a) · a ≡ e) (·-invʳ : ∀ a → a · (i a) ≡ e)
  → (·-comm : ∀ a b → a · b ≡ b · a)
  → AbelianGroup α α
eqsToAbelianGroup _·_ e i ·-assoc ·-idˡ ·-idʳ ·-invˡ ·-invʳ ·-comm = opsToBareGroup _·_ e i , proof
  where
  proof : opsToBareGroup _·_ e i ⊨ᵃᵍ Th-AbelianGroup
  proof assocᵃ ρ = ·-assoc (ρ 0F) (ρ 1F) (ρ 2F)
  proof idˡᵃ   ρ = ·-idˡ   (ρ 0F)
  proof idʳᵃ   ρ = ·-idʳ   (ρ 0F)
  proof invˡᵃ  ρ = ·-invˡ  (ρ 0F)
  proof invʳᵃ  ρ = ·-invʳ  (ρ 0F)
  proof comm   ρ = ·-comm  (ρ 0F) (ρ 1F)
```
