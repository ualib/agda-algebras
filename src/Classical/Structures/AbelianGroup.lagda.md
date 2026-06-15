---
layout: default
file: "src/Classical/Structures/AbelianGroup.lagda.md"
title: "Classical.Structures.AbelianGroup module"
date: "2026-05-30"
author: "the agda-algebras development team"
---

### Abelian Groups {#classical-structures-abeliangroup}

This is the [Classical.Structures.AbelianGroup][] module of the [Agda Universal Algebra Library][].

`Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ Th-AbelianGroup` over `Sig-Group`.  An equation-only
extension of Group, structurally identical to the way `CommutativeMonoid` extends
`Monoid`: `abelianGroup→group` is a pure theory-reindex (`proj₁` on the underlying
algebra), and `AbelianGroup-Op` inherits `_∙_`, `ε`, `_⁻¹`, and all five group laws
through it, adding `comm-law`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.AbelianGroup where

open import Agda.Primitive                          using () renaming ( Set to Type )

open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Level                                  using ( Level ; _⊔_ ; suc )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( _≡_ )

open import Classical.Signatures.Group             using ( Sig-Group )
open import Classical.Structures.Group             using ( Group ; module Group-Op ; opsToBareGroup )
open import Classical.Theories.Group               using ( assoc ; idˡ ; idʳ ; invˡ ; invʳ )
open import Classical.Theories.AbelianGroup        using ( Eq-AbelianGroup ; Th-AbelianGroup ; comm )
                                                   renaming ( assoc to assocᵃ ; idˡ to idˡᵃ ; idʳ to idʳᵃ
                                                            ; invˡ to invˡᵃ ; invʳ to invʳᵃ )
open import Overture.Terms {𝑆 = Sig-Group}         using ( Term ; ℊ )
open import Setoid.Algebras.Basic {𝑆 = Sig-Group}  using ( Algebra ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Varieties.EquationalLogic {𝑆 = Sig-Group} using ( _⊧_≈_ )

private variable α ρ : Level
```

#### Satisfaction predicate and the `AbelianGroup` type

```agda
infix 4 _⊨ᵃᵍ_
_⊨ᵃᵍ_ : (𝑨 : Algebra α ρ) (ℰ : Eq-AbelianGroup → Term (Fin 3) × Term (Fin 3)) → Type (α ⊔ ρ)
𝑨 ⊨ᵃᵍ ℰ = ∀ i → 𝑨 ⊧ proj₁ (ℰ i) ≈ proj₂ (ℰ i)

AbelianGroup : (α ρ : Level) → Type (suc α ⊔ suc ρ)
AbelianGroup α ρ = Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ᵃᵍ Th-AbelianGroup
```

#### The forgetful projection to groups

```agda
abelianGroup→group : AbelianGroup α ρ → Group α ρ
abelianGroup→group (𝑨 , mod) = 𝑨 , λ { assoc → mod assocᵃ
                                     ; idˡ   → mod idˡᵃ
                                     ; idʳ   → mod idʳᵃ
                                     ; invˡ  → mod invˡᵃ
                                     ; invʳ  → mod invʳᵃ }
```

#### The `AbelianGroup-Op` module

```agda
module AbelianGroup-Op {α ρ : Level} (𝑨𝑩 : AbelianGroup α ρ) where
  private 𝑨 = proj₁ 𝑨𝑩
  open Setoid 𝔻[ 𝑨 ]

  open Group-Op (abelianGroup→group 𝑨𝑩) public
    using ( _∙_ ; ε ; _⁻¹ ; ∙-cong ; ⁻¹-cong ; interp-node-∙ ; interp-node-ε ; interp-node-⁻¹
          ; assoc-law ; idˡ-law ; idʳ-law ; invˡ-law ; invʳ-law )

  equations : 𝑨 ⊨ᵃᵍ Th-AbelianGroup
  equations = proj₂ 𝑨𝑩

  comm-law : ∀ x y → x ∙ y ≈ y ∙ x
  comm-law x y = trans (sym (interp-node-∙ (ℊ 0F) (ℊ 1F) {η}))
                       (trans (equations comm η) (interp-node-∙ (ℊ 1F) (ℊ 0F) {η}))
    where η : Fin 3 → 𝕌[ 𝑨 ]
          η = λ { 0F → x ; 1F → y ; 2F → x }
```

#### `eqsToAbelianGroup`

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

--------------------------------------

<span style="float:left;">[← Classical.Structures.Group](Classical.Structures.Group.html)</span>
<span style="float:right;">[Classical.Structures.Ring →](Classical.Structures.Ring.html)</span>

{% include UALib.Links.md %}
