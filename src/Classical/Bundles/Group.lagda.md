---
layout: default
file: "src/Classical/Bundles/Group.lagda.md"
title: "Classical.Bundles.Group module"
date: "2026-05-30"
author: "the agda-algebras development team"
---

### Bundle bridge for groups

This is the [Classical.Bundles.Group][] module of the [Agda Universal Algebra Library][].

The bidirectional bridge between the Σ-typed core of [`Classical.Structures.Group`][]
and the record-typed `Algebra.Bundles.Group` in the standard library.  As with the
Monoid bridge, the round-trip is stated *pointwise* per
[ADR-002 v2 §6](../../docs/adr/002-classical-layer-design.md); the curried laws
`assoc-law`, `idˡ-law`, `idʳ-law`, `invˡ-law`, `invʳ-law` arrive ready-made from
`Group-Op`, so each direction is a thin record-shuffle.  The additions over the
Monoid bridge are the unary `_⁻¹` field, the `⁻¹-Op` clause of the reverse
interpretation, and the `inverse`/`⁻¹-cong` fields of `isGroup`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Bundles.Group where

-- Imports from the Agda Standard Library -----------------------------------------
open import Algebra.Bundles     using () renaming ( Group to stdlib-Group )
open import Data.Fin.Patterns   using ( 0F ; 1F ; 2F )
open import Data.Product        using ( _,_ ; proj₁ )
open import Function            using ( Func )
open import Level               using ( Level )
open import Relation.Binary     using ( Setoid )
import Relation.Binary.PropositionalEquality as ≡
open Func renaming ( to to _⟨$⟩_ )

-- Imports from the Agda Universal Algebra Library --------------------------------
open import Classical.Signatures.Group             using ( Sig-Group ; ∙-Op ; ε-Op ; ⁻¹-Op )
open import Classical.Structures.Group             using ( Group ; module Group-Op )
open import Classical.Theories.Group               using ( assoc ; idˡ ; idʳ ; invˡ ; invʳ )
open import Setoid.Algebras.Basic {𝑆 = Sig-Group}  using ( Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Signatures                      using  ( ⟨_⟩ )

private variable α ρ : Level
```

#### Core to stdlib bundle

```agda
⟨_⟩ᵍᵖ : Group α ρ → stdlib-Group α ρ
⟨ 𝑮 ⟩ᵍᵖ = record
  { Carrier = 𝕌[ 𝑨 ]
  ; _≈_     = _≈_
  ; _∙_     = _∙_
  ; ε       = ε
  ; _⁻¹     = _⁻¹
  ; isGroup = record
      { isMonoid = record
          { isSemigroup = record
              { isMagma = record { isEquivalence = isEquivalence ; ∙-cong = ∙-cong }
              ; assoc   = assoc-law
              }
          ; identity = idˡ-law , idʳ-law
          }
      ; inverse = invˡ-law , invʳ-law
      ; ⁻¹-cong = ⁻¹-cong
      }
  }
  where
  𝑨 = proj₁ 𝑮
  open Group-Op 𝑮
  open Setoid 𝔻[ 𝑨 ]
```

#### Stdlib bundle to core

```agda
⟪_⟫ᵍᵖ : stdlib-Group α ρ → Group α ρ
⟪ G ⟫ᵍᵖ = 𝑨 , λ { assoc ρ → G-assoc (ρ 0F) (ρ 1F) (ρ 2F)
                ; idˡ   ρ → G-idˡ   (ρ 0F)
                ; idʳ   ρ → G-idʳ   (ρ 0F)
                ; invˡ  ρ → G-invˡ  (ρ 0F)
                ; invʳ  ρ → G-invʳ  (ρ 0F) }
  where
  open stdlib-Group G
    using ( setoid ; ∙-cong ; ⁻¹-cong )
    renaming ( _∙_ to _·_ ; ε to e ; _⁻¹ to _⁻¹' ; assoc to G-assoc
             ; identityˡ to G-idˡ ; identityʳ to G-idʳ
             ; inverseˡ to G-invˡ ; inverseʳ to G-invʳ )

  𝑨 : Algebra _ _
  𝑨 = record { Domain = setoid ; Interp = interp }
    where
    interp : Func (⟨ Sig-Group ⟩ setoid) setoid
    interp ⟨$⟩ (∙-Op  , args)                             = args 0F · args 1F
    interp ⟨$⟩ (ε-Op  , _)                                = e
    interp ⟨$⟩ (⁻¹-Op , args)                             = (args 0F) ⁻¹'
    cong interp {∙-Op  , _} {.∙-Op  , _} (≡.refl , args≈) = ∙-cong (args≈ 0F) (args≈ 1F)
    cong interp {ε-Op  , _} {.ε-Op  , _} (≡.refl , _)     = Setoid.refl setoid
    cong interp {⁻¹-Op , _} {.⁻¹-Op , _} (≡.refl , args≈) = ⁻¹-cong (args≈ 0F)
```

#### Pointwise round-trip

```agda
module _ {𝑮 : Group α ρ} where
  open Group-Op 𝑮
  open Setoid 𝔻[ proj₁ 𝑮 ]
  open Group-Op ⟪ ⟨ 𝑮 ⟩ᵍᵖ ⟫ᵍᵖ renaming ( _∙_ to _∙'_ ; ε to ε' ; _⁻¹ to _⁻¹' )

  roundtrip-cbc-∙-group : (a b : 𝕌[ proj₁ 𝑮 ]) → (a ∙' b) ≈ (a ∙ b)
  roundtrip-cbc-∙-group a b = refl

  roundtrip-cbc-ε-group : ε' ≈ ε
  roundtrip-cbc-ε-group = refl

  roundtrip-cbc-⁻¹-group : (a : 𝕌[ proj₁ 𝑮 ]) → (a ⁻¹') ≈ (a ⁻¹)
  roundtrip-cbc-⁻¹-group a = refl

module _ {G : stdlib-Group α ρ} where
  open stdlib-Group G using ( _≈_ ; _∙_ ; ε ; _⁻¹ ; refl ) renaming ( Carrier to A )
  open stdlib-Group ⟨ ⟪ G ⟫ᵍᵖ ⟩ᵍᵖ using () renaming ( _∙_ to _∙'_ ; ε to ε' ; _⁻¹ to _⁻¹' )

  roundtrip-bcb-∙-group : (a b : A) → (a ∙ b) ≈ (a ∙' b)
  roundtrip-bcb-∙-group a b = refl

  roundtrip-bcb-ε-group : ε ≈ ε'
  roundtrip-bcb-ε-group = refl

  roundtrip-bcb-⁻¹-group : (a : A) → (a ⁻¹) ≈ (a ⁻¹')
  roundtrip-bcb-⁻¹-group a = refl
```

--------------------------------------

<span style="float:left;">[← Classical.Structures.Group](Classical.Structures.Group.html)</span>
<span style="float:right;">[Classical.Bundles.AbelianGroup →](Classical.Bundles.AbelianGroup.html)</span>

{% include UALib.Links.md %}
