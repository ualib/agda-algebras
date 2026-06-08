---
layout: default
file: "src/Setoid/Categories/Functor.lagda.md"
title: "Setoid.Categories.Functor module"
date: "2026-06-08"
author: "the agda-algebras development team"
---

### Functors between minimal categories

This is the [Setoid.Categories.Functor][] module of the [Agda Universal Algebra Library][].

A `Functor 𝒞 𝒟` between [`Category`][Setoid.Categories.Category] records: an object map `F₀`,
a hom map `F₁` that respects each hom-set's equivalence (`F-resp-≈`), and the two functor laws
(`identity`, `homomorphism`) stated up to the *target* category's hom-equality `𝒟 [ _≈_ ]`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Categories.Functor where

open import Agda.Primitive  using ( _⊔_ ) renaming ( Set to Type )
open import Level           using ( Level )

open import Setoid.Categories.Category using ( Category )

private variable o ℓ e o′ ℓ′ e′ : Level

record Functor (𝒞 : Category o ℓ e) (𝒟 : Category o′ ℓ′ e′)
  : Type (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private module C = Category 𝒞
  private module D = Category 𝒟
  field
    F₀ : C.Obj → D.Obj
    F₁ : {A B : C.Obj} → A C.⇒ B → F₀ A D.⇒ F₀ B

    F-resp-≈     : {A B : C.Obj} {f g : A C.⇒ B} → f C.≈ g → F₁ f D.≈ F₁ g
    identity     : {A : C.Obj} → F₁ (C.id {A}) D.≈ D.id
    homomorphism : {A B E : C.Obj} {f : A C.⇒ B} {g : B C.⇒ E}
                 → F₁ (g C.∘ f) D.≈ (F₁ g D.∘ F₁ f)
```

--------------------------------------

{% include UALib.Links.md %}
