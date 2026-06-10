---
layout: default
file: "src/Setoid/Categories/Adjunction.lagda.md"
title: "Setoid.Categories.Adjunction module"
date: "2026-06-10"
author: "the agda-algebras development team"
---

### Adjunctions between minimal categories

This is the [Setoid.Categories.Adjunction][] module of the [Agda Universal Algebra Library][].

An `Adjunction L R` exhibits the functor `L : 𝒞 ⟶ 𝒟` as *left adjoint* to
`R : 𝒟 ⟶ 𝒞`.  Following the self-contained realization of ADR-006, the record is
*componentwise*: a family `unit` of `𝒞`-morphisms `A ⟶ R (L A)` and a family
`counit` of `𝒟`-morphisms `L (R B) ⟶ B`, each with its naturality square, together
with the two triangle identities — `zig` (the counit–unit triangle at `L`,
`counit (L A) ∘ L (unit A) ≈ id`) and `zag` (the triangle at `R`,
`R (counit B) ∘ unit (R B) ≈ id`).  Packaging `unit` and `counit` as
natural-transformation records is deferred to M4-5e, which introduces them for the
`Term` monad; the componentwise form is exactly what the free-expansion spike of
M4-5d consumes.

Every law is stated against the owning category's hom-equality `_≈_`, so an
instance whose hom-equality is pointwise (the algebra categories of
[Setoid.Categories.Algebra][]) proves the triangles pointwise, with no funext.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Categories.Adjunction where

open import Agda.Primitive  using ( _⊔_ ) renaming ( Set to Type )
open import Level           using ( Level )

open import Setoid.Categories.Category using ( Category )
open import Setoid.Categories.Functor  using ( Functor )

private variable o ℓ e o′ ℓ′ e′ : Level

record Adjunction {𝒞 : Category o ℓ e} {𝒟 : Category o′ ℓ′ e′}
                  (L : Functor 𝒞 𝒟) (R : Functor 𝒟 𝒞) : Type (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  open Category 𝒞 renaming ( Obj to Obj₀ ; Hom to Hom₀ ; _≈_ to _≈₀_ ; id to id₀ ; _∘_ to _∘₀_ )
  open Category 𝒟 renaming ( Obj to Obj₁ ; Hom to Hom₁ ; _≈_ to _≈₁_ ; id to id₁ ; _∘_ to _∘₁_ )
  open Functor L renaming ( F₀ to L₀ ; F₁ to L₁ )
  open Functor R renaming ( F₀ to R₀ ; F₁ to R₁ )

  field
    -- The unit and counit components: η_A : A ⟶ R (L A) and ε_B : L (R B) ⟶ B.
    unit   : (A : Obj₀) → Hom₀ A (R₀ (L₀ A))
    counit : (B : Obj₁) → Hom₁ (L₀ (R₀ B)) B

    -- Naturality of each family.
    unit-natural   : {A B : Obj₀} (f : Hom₀ A B)
                   → (unit B ∘₀ f) ≈₀ (R₁ (L₁ f) ∘₀ unit A)
    counit-natural : {A B : Obj₁} (g : Hom₁ A B)
                   → (counit B ∘₁ L₁ (R₁ g)) ≈₁ (g ∘₁ counit A)

    -- The triangle identities.
    zig : (A : Obj₀) → (counit (L₀ A) ∘₁ L₁ (unit A)) ≈₁ id₁ {L₀ A}
    zag : (B : Obj₁) → (R₁ (counit B) ∘₀ unit (R₀ B)) ≈₀ id₀ {R₀ B}
```

--------------------------------------

{% include UALib.Links.md %}
