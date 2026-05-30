---
layout: default
file: "src/Classical/Structures/CommutativeRing.lagda.md"
title: "Classical.Structures.CommutativeRing module"
date: "2026-05-30"
author: "the agda-algebras development team"
---

### Commutative Rings {#classical-structures-commutativering}

This is the [Classical.Structures.CommutativeRing][] module of the [Agda Universal Algebra Library][].

`Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ Th-CommutativeRing` over `Sig-Ring`.  An equation-only
extension of Ring, structurally identical to the way `CommutativeMonoid` extends
`Monoid` and `AbelianGroup` extends `Group`: `commutativeRing→ring` is a pure
theory-reindex (`proj₁` on the underlying algebra), and `CommutativeRing-Op` inherits
the additive `(_+_, 0R, -_)`, the multiplicative `(_·_, 1R)`, and all eleven ring laws
through it, adding `·-comm-law`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.CommutativeRing where

open import Agda.Primitive                          using () renaming ( Set to Type )

open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Level                                  using ( Level ; _⊔_ ; suc )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( _≡_ )

open import Classical.Signatures.Ring              using ( Sig-Ring )
open import Classical.Structures.Ring              using ( Ring ; module Ring-Op ; opsToBareRing )
open import Classical.Theories.Ring                using ( +-assoc ; +-idˡ ; +-idʳ ; +-invˡ ; +-invʳ ; +-comm
                                                         ; ·-assoc ; ·-idˡ ; ·-idʳ ; distribˡ ; distribʳ )
open import Classical.Theories.CommutativeRing     using ( Eq-CommutativeRing ; Th-CommutativeRing ; ·-comm )
                                                   renaming ( +-assoc to +-assocᶜ ; +-idˡ to +-idˡᶜ ; +-idʳ to +-idʳᶜ
                                                            ; +-invˡ to +-invˡᶜ ; +-invʳ to +-invʳᶜ ; +-comm to +-commᶜ
                                                            ; ·-assoc to ·-assocᶜ ; ·-idˡ to ·-idˡᶜ ; ·-idʳ to ·-idʳᶜ
                                                            ; distribˡ to distribˡᶜ ; distribʳ to distribʳᶜ )
open import Overture.Terms {𝑆 = Sig-Ring}          using ( Term ; ℊ )
open import Setoid.Algebras.Basic {𝑆 = Sig-Ring}   using ( Algebra ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Varieties.EquationalLogic {𝑆 = Sig-Ring} using ( _⊧_≈_ )

private variable α ρ : Level
```

#### Satisfaction predicate and the `CommutativeRing` type

```agda
infix 4 _⊨ᶜʳᵍ_
_⊨ᶜʳᵍ_ : (𝑨 : Algebra α ρ) (ℰ : Eq-CommutativeRing → Term (Fin 3) × Term (Fin 3)) → Type (α ⊔ ρ)
𝑨 ⊨ᶜʳᵍ ℰ = ∀ i → 𝑨 ⊧ proj₁ (ℰ i) ≈ proj₂ (ℰ i)

CommutativeRing : (α ρ : Level) → Type (suc α ⊔ suc ρ)
CommutativeRing α ρ = Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ᶜʳᵍ Th-CommutativeRing
```

#### The forgetful projection to rings

```agda
commutativeRing→ring : CommutativeRing α ρ → Ring α ρ
commutativeRing→ring (𝑨 , mod) = 𝑨 , λ  { +-assoc   → mod +-assocᶜ
                                        ; +-idˡ     → mod +-idˡᶜ
                                        ; +-idʳ     → mod +-idʳᶜ
                                        ; +-invˡ    → mod +-invˡᶜ
                                        ; +-invʳ    → mod +-invʳᶜ
                                        ; +-comm    → mod +-commᶜ
                                        ; ·-assoc   → mod ·-assocᶜ
                                        ; ·-idˡ     → mod ·-idˡᶜ
                                        ; ·-idʳ     → mod ·-idʳᶜ
                                        ; distribˡ  → mod distribˡᶜ
                                        ; distribʳ  → mod distribʳᶜ }
```

#### The `CommutativeRing-Op` module

```agda
module CommutativeRing-Op {α ρ : Level} (𝑪 : CommutativeRing α ρ) where
  private 𝑨 = proj₁ 𝑪
  open Setoid 𝔻[ 𝑨 ]

  open Ring-Op (commutativeRing→ring 𝑪) public
    using ( _+_ ; _·_ ; 0R ; 1R ; -_ ; +-cong ; ·-cong ; neg-cong
          ; interp-node-+ ; interp-node-· ; interp-node-0 ; interp-node-1 ; interp-node-neg
          ; +-assoc-law ; +-idˡ-law ; +-idʳ-law ; +-invˡ-law ; +-invʳ-law ; +-comm-law
          ; ·-assoc-law ; ·-idˡ-law ; ·-idʳ-law ; distribˡ-law ; distribʳ-law )

  equations : 𝑨 ⊨ᶜʳᵍ Th-CommutativeRing
  equations = proj₂ 𝑪

  ·-comm-law : ∀ x y → x · y ≈ y · x
  ·-comm-law x y = trans (sym (interp-node-· (ℊ 0F) (ℊ 1F) {η}))
                         (trans (equations ·-comm η) (interp-node-· (ℊ 1F) (ℊ 0F) {η}))
    where η : Fin 3 → 𝕌[ 𝑨 ]
          η = λ { 0F → x ; 1F → y ; 2F → x }
```

#### `eqsToCommutativeRing`

```agda
eqsToCommutativeRing : (A : Type α) (_+'_ : A → A → A) (0' : A) (-'_ : A → A) (_*'_ : A → A → A) (1' : A)
  → (+-assoc-≡ : ∀ a b c → (a +' b) +' c ≡ a +' (b +' c))
  → (+-idˡ-≡ : ∀ a → 0' +' a ≡ a) (+-idʳ-≡ : ∀ a → a +' 0' ≡ a)
  → (+-invˡ-≡ : ∀ a → (-' a) +' a ≡ 0') (+-invʳ-≡ : ∀ a → a +' (-' a) ≡ 0')
  → (+-comm-≡ : ∀ a b → a +' b ≡ b +' a)
  → (*-assoc-≡ : ∀ a b c → (a *' b) *' c ≡ a *' (b *' c))
  → (*-idˡ-≡ : ∀ a → 1' *' a ≡ a) (*-idʳ-≡ : ∀ a → a *' 1' ≡ a)
  → (*-comm-≡ : ∀ a b → a *' b ≡ b *' a)
  → (distribˡ-≡ : ∀ a b c → a *' (b +' c) ≡ (a *' b) +' (a *' c))
  → (distribʳ-≡ : ∀ a b c → (b +' c) *' a ≡ (b *' a) +' (c *' a))
  → CommutativeRing α α
eqsToCommutativeRing A _+'_ 0' -'_ _*'_ 1'
  +-assoc-≡ +-idˡ-≡ +-idʳ-≡ +-invˡ-≡ +-invʳ-≡ +-comm-≡ *-assoc-≡ *-idˡ-≡ *-idʳ-≡ *-comm-≡ distribˡ-≡ distribʳ-≡ =
  opsToBareRing A _+'_ 0' -'_ _*'_ 1' , proof
  where
  proof : opsToBareRing A _+'_ 0' -'_ _*'_ 1' ⊨ᶜʳᵍ Th-CommutativeRing
  proof +-assocᶜ  ρ = +-assoc-≡  (ρ 0F) (ρ 1F) (ρ 2F)
  proof +-idˡᶜ    ρ = +-idˡ-≡    (ρ 0F)
  proof +-idʳᶜ    ρ = +-idʳ-≡    (ρ 0F)
  proof +-invˡᶜ   ρ = +-invˡ-≡   (ρ 0F)
  proof +-invʳᶜ   ρ = +-invʳ-≡   (ρ 0F)
  proof +-commᶜ   ρ = +-comm-≡   (ρ 0F) (ρ 1F)
  proof ·-assocᶜ  ρ = *-assoc-≡  (ρ 0F) (ρ 1F) (ρ 2F)
  proof ·-idˡᶜ    ρ = *-idˡ-≡    (ρ 0F)
  proof ·-idʳᶜ    ρ = *-idʳ-≡    (ρ 0F)
  proof ·-comm    ρ = *-comm-≡   (ρ 0F) (ρ 1F)
  proof distribˡᶜ ρ = distribˡ-≡ (ρ 0F) (ρ 1F) (ρ 2F)
  proof distribʳᶜ ρ = distribʳ-≡ (ρ 0F) (ρ 1F) (ρ 2F)
```

--------------------------------------

<span style="float:left;">[← Classical.Structures.Ring](Classical.Structures.Ring.html)</span>

{% include UALib.Links.md %}
