---
layout: default
title : "Setoid.Homomorphisms.Products module (The Agda Universal Algebra Library)"
date : "2021-09-21"
author: "agda-algebras development team"
---

#### Products of Homomorphisms of Algebras

This is the [Setoid.Homomorphisms.Products][] module of the [Agda Universal Algebra Library][].

This module defines some of the homomorphisms associated with a product.

+  `⨅-hom-co`{.AgdaFunction} is the induced map into a product: a family of homomorphisms out
   of a single algebra `𝑨`, one for each index, assembles into a single homomorphism
   from `𝑨` to the product;
+  `⨅-hom`{.AgdaFunction} takes a family of homomorphisms `𝒜 i → ℬ i` to their
   product, `⨅ 𝒜 → ⨅ ℬ`;
+  `⨅-proj`{.AgdaFunction} is the coordinate projection `⨅ 𝒜 → 𝒜 i`;
+  `×-proj₁`{.AgdaFunction}, `×-proj₂`{.AgdaFunction}, and
   `×-hom-co`{.AgdaFunction} are the same constructions for the binary product
   `_×ᴬ_`{.AgdaFunction}: the two projections, and the pairing of two
   homomorphisms out of `𝑨`.

All three are defined coordinatewise, and their compatibility proofs are inherited
coordinatewise from the factors, because that is how `⨅`{.AgdaFunction} of
[Setoid.Algebras.Products][] interprets the operations in the first place.[^1]

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Setoid.Homomorphisms.Products where

-- Imports from Agda and the Agda Standard Library --------------------------
open import Agda.Primitive              using () renaming ( Set to Type )
open import Function                    using () renaming ( Func to _⟶_ )
open import Data.Product                using ( _,_ )
open import Level                       using ( Level )
open import Relation.Binary             using ( Setoid )

-- Imports from the Agda Universal Algebras Library ----------------------
open import Overture                    using ( proj₁ ; proj₂ ; 𝓞 ; 𝓥 ; Signature)
open import Setoid.Algebras             using ( Algebra ; ⨅ ; 𝔻[_] ; _×ᴬ_ )
open import Setoid.Homomorphisms.Basic  using ( hom ; IsHom )

open _⟶_ using ( cong )  renaming ( to to _⟨$⟩_ )
open IsHom

private variable α ρ β ρᵇ γ ρᶜ 𝓘 : Level
```
-->

Suppose we have an algebra `𝑨`, a type `I : Type 𝓘`, and a family
`ℬ : I → Algebra β 𝑆` of algebras.  We sometimes refer to the inhabitants of `I`
as *indices*, and call `ℬ` an *indexed family of algebras*.

If in addition we have a family `𝒽 : (i : I) → hom 𝑨 (ℬ i)` of homomorphisms, then
we can construct a homomorphism from `𝑨` to the product `⨅ ℬ` in the natural way.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ } {I : Type 𝓘} (ℬ : I → Algebra β ρᵇ)  where

  ⨅-hom-co : (∀(i : I) → hom 𝑨 (ℬ i)) → hom 𝑨 (⨅ ℬ)
  ⨅-hom-co 𝒽 = h , hhom
    where
    h : 𝔻[ 𝑨 ] ⟶ 𝔻[ ⨅ ℬ ]
    h ⟨$⟩ a = λ i → 𝒽 i .proj₁ ⟨$⟩ a
    h .cong xy = λ i → 𝒽 i .proj₁ .cong xy

    hhom : IsHom 𝑨 (⨅ ℬ) h
    hhom .compatible = λ i → 𝒽 i .proj₂ .compatible
```

If we are given `𝒜 : I → Algebra α 𝑆` and `ℬ : I → Algebra β 𝑆`
(two families of `𝑆`-algebras), then a family `𝒽` of homomorphisms inhabits the
dependent type `∀ (i : I) → hom (𝒜 i) (ℬ i)`, from which we construct a homomorphism
from `⨅ 𝒜` to `⨅ ℬ` in the following natural way.

```agda
module _  {𝑆 : Signature 𝓞 𝓥} {I : Type 𝓘} (𝒜 : I → Algebra {𝑆 = 𝑆} α ρ) where
  ⨅-hom : (ℬ : I → Algebra β ρᵇ) → (∀ (i : I) → hom (𝒜 i) (ℬ i)) → hom (⨅ 𝒜)(⨅ ℬ)
  ⨅-hom ℬ 𝒽 = F , isHom
    where

    F : 𝔻[ ⨅ 𝒜 ] ⟶ 𝔻[ ⨅ ℬ ]
    F ⟨$⟩ x = λ i → 𝒽 i .proj₁ ⟨$⟩ x i
    F .cong xy = λ i → 𝒽 i .proj₁ .cong (xy i)

    isHom : IsHom (⨅ 𝒜) (⨅ ℬ) F
    isHom .compatible = λ i → 𝒽 i .proj₂ .compatible
```


#### Projection out of products

The projection of a product algebra onto its `i`-th factor is a homomorphism.

```agda
  ⨅-proj : (i : I) → hom (⨅ 𝒜) (𝒜 i)
  ⨅-proj i = F , isHom
    where
    F : 𝔻[ ⨅ 𝒜 ] ⟶ 𝔻[ 𝒜 i ]
    F ⟨$⟩ x = x i
    F .cong xy = xy i

    isHom : IsHom (⨅ 𝒜) (𝒜 i) F
    isHom .compatible = Setoid.refl 𝔻[ 𝒜 i ]
```

We could prove a more general result involving projections onto multiple factors, but
so far the single-factor result has sufficed.

#### Homomorphisms of binary products

The two projections out of a binary product `𝑩 ×ᴬ 𝑪`{.AgdaFunction} are
homomorphisms, `×-proj₁`{.AgdaFunction} onto `𝑩` and `×-proj₂`{.AgdaFunction} onto
`𝑪`; the setoid equality of the product is the conjunction of the two coordinate
equalities, so each projection respects it by taking one conjunct.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑩 : Algebra {𝑆 = 𝑆} β ρᵇ} {𝑪 : Algebra {𝑆 = 𝑆} γ ρᶜ} where
  -- The first projection 𝑩 × 𝑪 → 𝑩.
  ×-proj₁ : hom (𝑩 ×ᴬ 𝑪) 𝑩
  ×-proj₁ = F , isHom
    where
    F : 𝔻[ 𝑩 ×ᴬ 𝑪 ] ⟶ 𝔻[ 𝑩 ]
    F ⟨$⟩ x = proj₁ x
    F .cong xy = proj₁ xy

    isHom : IsHom (𝑩 ×ᴬ 𝑪) 𝑩 F
    isHom .compatible = Setoid.refl 𝔻[ 𝑩 ]

  -- The second projection 𝑩 × 𝑪 → 𝑪.
  ×-proj₂ : hom (𝑩 ×ᴬ 𝑪) 𝑪
  ×-proj₂ = F , isHom
    where
    F : 𝔻[ 𝑩 ×ᴬ 𝑪 ] ⟶ 𝔻[ 𝑪 ]
    F ⟨$⟩ x = proj₂ x
    F .cong xy = proj₂ xy

    isHom : IsHom (𝑩 ×ᴬ 𝑪) 𝑪 F
    isHom .compatible = Setoid.refl 𝔻[ 𝑪 ]
```

Two homomorphisms `g : 𝑨 → 𝑩` and `h : 𝑨 → 𝑪` out of one algebra pair to the
homomorphism `×-hom-co g h : 𝑨 → 𝑩 ×ᴬ 𝑪`{.AgdaFunction}, `a ↦ (g a , h a)`; it is
the binary case of `⨅-hom-co`{.AgdaFunction}, and composing it with either
projection gives back `g` or `h` on the nose.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ}
         {𝑩 : Algebra {𝑆 = 𝑆} β ρᵇ} {𝑪 : Algebra {𝑆 = 𝑆} γ ρᶜ} where
  -- The pairing a ↦ (g a , h a) of two homomorphisms out of 𝑨.
  ×-hom-co : hom 𝑨 𝑩 → hom 𝑨 𝑪 → hom 𝑨 (𝑩 ×ᴬ 𝑪)
  ×-hom-co g h = F , isHom
    where
    F : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ×ᴬ 𝑪 ]
    F ⟨$⟩ a = g .proj₁ ⟨$⟩ a , h .proj₁ ⟨$⟩ a
    F .cong xy = g .proj₁ .cong xy , h .proj₁ .cong xy

    isHom : IsHom 𝑨 (𝑩 ×ᴬ 𝑪) F
    isHom .compatible = g .proj₂ .compatible , h .proj₂ .compatible
```

---

[^1]: `⨅-hom-co`{.AgdaFunction} does real work later: the proof of Birkhoff's theorem
      in [Setoid.Varieties.HSP][] uses it to build the homomorphism `homℭ` from the
      term algebra into the product `ℭ` that the whole argument turns on.

