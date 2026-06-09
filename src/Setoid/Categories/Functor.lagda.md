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

record Functor (𝒞 : Category o ℓ e) (𝒟 : Category o′ ℓ′ e′) : Type (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  open Category 𝒞 renaming (Obj to Obj₀; Hom to Hom₀; _≈_ to _≈₀_; id to id₀; _∘_ to _∘₀_)
  open Category 𝒟 renaming (Obj to Obj₁; Hom to Hom₁; _≈_ to _≈₁_; id to id₁; _∘_ to _∘₁_)
  field
    F₀ : Obj₀ → Obj₁
    F₁ : {A B : Obj₀} → Hom₀ A B → Hom₁ (F₀ A) (F₀ B)

    F-resp-≈      : {A B : Obj₀} {f g : Hom₀ A B} → f ≈₀ g → F₁ f ≈₁ F₁ g
    identity      : {A : Obj₀} → F₁ (id₀ {A}) ≈₁ id₁
    homomorphism  : {A B E : Obj₀} {f : Hom₀ A B} {g : Hom₀ B E} → F₁ (g ∘₀ f) ≈₁ (F₁ g ∘₁ F₁ f)
```

--------------------------------------

{% include UALib.Links.md %}
