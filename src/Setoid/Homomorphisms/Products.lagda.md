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
+  `⨅-proj`{.AgdaFunction} is the coordinate projection `⨅ 𝒜 → 𝒜 i`.

All three are defined coordinatewise, and their compatibility proofs are inherited
coordinatewise from the factors, because that is how `⨅`{.AgdaFunction} of
[Setoid.Algebras.Products][] interprets the operations in the first place.[^1]

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Homomorphisms.Products where

-- Imports from Agda and the Agda Standard Library --------------------------
open import Agda.Primitive              using () renaming ( Set to Type )
open import Function                    using () renaming ( Func to _⟶_ )
open import Data.Product                using ( _,_ )
open import Level                       using ( Level )
open import Relation.Binary             using ( Setoid )

-- Imports from the Agda Universal Algebras Library ----------------------
open import Overture                    using ( proj₁ ; proj₂ ; 𝓞 ; 𝓥 ; Signature)
open import Setoid.Algebras             using ( Algebra ; ⨅ ; 𝔻[_] )
open import Setoid.Homomorphisms.Basic  using ( hom ; IsHom )

open _⟶_ using ( cong )  renaming ( to to _⟨$⟩_ )
open IsHom

private variable α ρ β ρᵇ 𝓘 : Level
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

---

[^1]: `⨅-hom-co`{.AgdaFunction} does real work later: the proof of Birkhoff's theorem
      in [Setoid.Varieties.HSP][] uses it to build the homomorphism `homℭ` from the
      term algebra into the product `ℭ` that the whole argument turns on.

