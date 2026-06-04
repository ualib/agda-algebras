---
layout: default
file: "src/Classical/Bundles/CommutativeRing.lagda.md"
title: "Classical.Bundles.CommutativeRing module"
date: "2026-05-30"
author: "the agda-algebras development team"
---

### Bundle bridge for commutative rings

This is the [Classical.Bundles.CommutativeRing][] module of the [Agda Universal Algebra Library][].

Mirror of the Ring bridge with the added `*-comm` field; over `Sig-Ring`.  This is the
bridge whose round-trip on `ℤ` is exercised in
[`Examples.Classical.CommutativeRing`][].

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Bundles.CommutativeRing where

-- Imports from the Agda Standard Library -----------------------------------------
open import Algebra.Bundles     using () renaming ( CommutativeRing to stdlib-CommutativeRing )
open import Data.Fin.Patterns   using ( 0F ; 1F ; 2F )
open import Data.Product        using ( _,_ ; proj₁ )
open import Function            using ( Func )
open import Level               using ( Level )
open import Relation.Binary     using ( Setoid )
import Relation.Binary.PropositionalEquality as ≡
open Func renaming ( to to _⟨$⟩_ )

-- Imports from the Agda Universal Algebra Library --------------------------------
open import Classical.Signatures.Ring             using ( Sig-Ring ; +-Op ; 0-Op ; -Op ; ·-Op ; 1-Op )
open import Classical.Structures.CommutativeRing  using ( CommutativeRing ; module CommutativeRing-Op )
open import Classical.Theories.CommutativeRing    using ( +-assoc ; +-idˡ ; +-idʳ ; +-invˡ ; +-invʳ ; +-comm
                                                        ; ·-assoc ; ·-idˡ ; ·-idʳ ; ·-comm ; distribˡ ; distribʳ )
open import Setoid.Algebras.Basic {𝑆 = Sig-Ring}  using ( Algebra ; ⟨_⟩ ; 𝕌[_] ; 𝔻[_] )

private variable α ρ : Level
```

#### Core to stdlib bundle

```agda
⟨_⟩ᶜʳᵍ : CommutativeRing α ρ → stdlib-CommutativeRing α ρ
⟨ 𝑪 ⟩ᶜʳᵍ = record
  { Carrier = 𝕌[ proj₁ 𝑪 ]
  ; _≈_     = _≈_
  ; _+_     = _+_
  ; _*_     = _·_
  ; -_      = -_
  ; 0#      = 0R
  ; 1#      = 1R
  ; isCommutativeRing = record
      { isRing = record
          { +-isAbelianGroup = record
              { isGroup = record
                  { isMonoid = record
                      { isSemigroup = record
                          { isMagma = record { isEquivalence = isEquivalence ; ∙-cong = +-cong }
                          ; assoc   = +-assoc-law
                          }
                      ; identity = +-idˡ-law , +-idʳ-law
                      }
                  ; inverse = +-invˡ-law , +-invʳ-law
                  ; ⁻¹-cong = neg-cong
                  }
              ; comm = +-comm-law
              }
          ; *-cong     = ·-cong
          ; *-assoc    = ·-assoc-law
          ; *-identity = ·-idˡ-law , ·-idʳ-law
          ; distrib    = distribˡ-law , distribʳ-law
          }
      ; *-comm = ·-comm-law
      }
  }
  where
  open CommutativeRing-Op 𝑪
  open Setoid 𝔻[ proj₁ 𝑪 ]
```

#### Stdlib bundle to core

```agda
⟪_⟫ᶜʳᵍ : stdlib-CommutativeRing α ρ → CommutativeRing α ρ
⟪ R ⟫ᶜʳᵍ = 𝑨 , λ { +-assoc  ρ → R-+assoc   (ρ 0F) (ρ 1F) (ρ 2F)
                 ; +-idˡ    ρ → R-+idˡ     (ρ 0F)
                 ; +-idʳ    ρ → R-+idʳ     (ρ 0F)
                 ; +-invˡ   ρ → R-+invˡ    (ρ 0F)
                 ; +-invʳ   ρ → R-+invʳ    (ρ 0F)
                 ; +-comm   ρ → R-+comm    (ρ 0F) (ρ 1F)
                 ; ·-assoc  ρ → R-*assoc   (ρ 0F) (ρ 1F) (ρ 2F)
                 ; ·-idˡ    ρ → R-*idˡ     (ρ 0F)
                 ; ·-idʳ    ρ → R-*idʳ     (ρ 0F)
                 ; ·-comm   ρ → R-*comm    (ρ 0F) (ρ 1F)
                 ; distribˡ ρ → R-distribˡ (ρ 0F) (ρ 1F) (ρ 2F)
                 ; distribʳ ρ → R-distribʳ (ρ 0F) (ρ 1F) (ρ 2F) }
  where
  open stdlib-CommutativeRing R
      using ( setoid ; +-cong ; -‿cong ; *-cong )
      renaming ( _+_ to _⊕_ ; _*_ to _⊛_ ; -_ to ⊖_ ; 0# to z ; 1# to o
               ; +-assoc to R-+assoc ; +-identityˡ to R-+idˡ ; +-identityʳ to R-+idʳ
               ; -‿inverseˡ to R-+invˡ ; -‿inverseʳ to R-+invʳ ; +-comm to R-+comm
               ; *-assoc to R-*assoc ; *-identityˡ to R-*idˡ ; *-identityʳ to R-*idʳ
               ; *-comm to R-*comm ; distribˡ to R-distribˡ ; distribʳ to R-distribʳ )

  𝑨 : Algebra _ _
  𝑨 = record { Domain = setoid ; Interp = interp }
    where
    interp : Func (⟨ Sig-Ring ⟩ setoid) setoid
    interp ⟨$⟩ (+-Op , args)                             = args 0F ⊕ args 1F
    interp ⟨$⟩ (0-Op , _)                                = z
    interp ⟨$⟩ (-Op  , args)                             = ⊖ (args 0F)
    interp ⟨$⟩ (·-Op , args)                             = args 0F ⊛ args 1F
    interp ⟨$⟩ (1-Op , _)                                = o
    cong interp {+-Op , _} {.+-Op , _} (≡.refl , args≈)  = +-cong (args≈ 0F) (args≈ 1F)
    cong interp {0-Op , _} {.0-Op , _} (≡.refl , _)      = Setoid.refl setoid
    cong interp { -Op , _} {.-Op  , _} (≡.refl , args≈)  = -‿cong (args≈ 0F)
    cong interp {·-Op , _} {.·-Op , _} (≡.refl , args≈)  = *-cong (args≈ 0F) (args≈ 1F)
    cong interp {1-Op , _} {.1-Op , _} (≡.refl , _)      = Setoid.refl setoid
```

#### Pointwise round-trip

```agda
module _ {𝑪 : CommutativeRing α ρ} where
  open CommutativeRing-Op 𝑪
  open Setoid 𝔻[ proj₁ 𝑪 ]
  open CommutativeRing-Op ⟪ ⟨ 𝑪 ⟩ᶜʳᵍ ⟫ᶜʳᵍ renaming ( _+_ to _+'_ ; _·_ to _·'_ ; -_ to -'_ ; 0R to 0R' ; 1R to 1R' )

  roundtrip-cbc-+-cr : (a b : 𝕌[ proj₁ 𝑪 ]) → (a +' b) ≈ (a + b)
  roundtrip-cbc-+-cr a b = refl

  roundtrip-cbc-·-cr : (a b : 𝕌[ proj₁ 𝑪 ]) → (a ·' b) ≈ (a · b)
  roundtrip-cbc-·-cr a b = refl

  roundtrip-cbc-neg-cr : (a : 𝕌[ proj₁ 𝑪 ]) → (-' a) ≈ (- a)
  roundtrip-cbc-neg-cr a = refl

  roundtrip-cbc-0-cr : 0R' ≈ 0R
  roundtrip-cbc-0-cr = refl

  roundtrip-cbc-1-cr : 1R' ≈ 1R
  roundtrip-cbc-1-cr = refl

module _ {R : stdlib-CommutativeRing α ρ} where
  open stdlib-CommutativeRing R using ( _≈_ ; _+_ ; _*_ ; -_ ; 0# ; 1# ; refl ) renaming ( Carrier to A )
  open stdlib-CommutativeRing ⟨ ⟪ R ⟫ᶜʳᵍ ⟩ᶜʳᵍ using () renaming ( _+_ to _+'_ ; _*_ to _*'_ ; -_ to -'_ ; 0# to 0#' ; 1# to 1#' )

  roundtrip-bcb-+-cr : (a b : A) → (a + b) ≈ (a +' b)
  roundtrip-bcb-+-cr a b = refl

  roundtrip-bcb-·-cr : (a b : A) → (a * b) ≈ (a *' b)
  roundtrip-bcb-·-cr a b = refl

  roundtrip-bcb-neg-cr : (a : A) → (- a) ≈ (-' a)
  roundtrip-bcb-neg-cr a = refl

  roundtrip-bcb-0-cr : 0# ≈ 0#'
  roundtrip-bcb-0-cr = refl

  roundtrip-bcb-1-cr : 1# ≈ 1#'
  roundtrip-bcb-1-cr = refl
```

--------------------------------------

<span style="float:left;">[← Classical.Structures.CommutativeRing](Classical.Structures.CommutativeRing.html)</span>

{% include UALib.Links.md %}
