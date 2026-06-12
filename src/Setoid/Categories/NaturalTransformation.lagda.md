---
layout: default
file: "src/Setoid/Categories/NaturalTransformation.lagda.md"
title: "Setoid.Categories.NaturalTransformation module"
date: "2026-06-12"
author: "the agda-algebras development team"
---

### Natural transformations between minimal functors

This is the [Setoid.Categories.NaturalTransformation][] module of the [Agda Universal Algebra Library][].

A *natural transformation* is the third rung of the basic category-theory ladder, after
[`Category`][Setoid.Categories.Category] and [`Functor`][Setoid.Categories.Functor], and it
is the notion category theory was invented to make precise.  Where a functor `F : 𝒞 ⟶ 𝒟`
translates one mathematical world into another, a natural transformation compares two such
translations `F, G : 𝒞 ⟶ 𝒟`: it assigns to every object `A` of `𝒞` a `𝒟`-morphism
`component A : F₀ A ⟶ G₀ A`, in a way that is *uniform* in `A`.

Uniformity is the entire content of the definition.  The components must not be ad-hoc
choices made object by object; they must commute with every morphism of `𝒞`, which the
`natural`{.AgdaField} field states as the famous *naturality square*: for each
`f : A ⟶ B` in `𝒞`,

```text
                component A
        F₀ A ───────────────→ G₀ A
          │                     │
     F₁ f │                     │ G₁ f
          ↓                     ↓
        F₀ B ───────────────→ G₀ B
                component B
```

both ways around the square are the same `𝒟`-morphism — `component B ∘ F₁ f` equals
`G₁ f ∘ component A` — up to the *target* category's hom-equality `_≈_`.  Intuitively:
first translate by `F` and then convert to `G`, or convert first and then translate by
`G`; naturality says it cannot matter.  A family of maps with this property is exactly
what a working mathematician means by a construction that "requires no arbitrary
choices."

The library has already met this notion twice, componentwise:

+  A signature morphism `φ : 𝑆₁ → 𝑆₂` induces the family
   `⟦ φ ⟧ A : ⟨ 𝑆₁ ⟩ A ⟶ ⟨ 𝑆₂ ⟩ A` of [Setoid.Signatures.Functor][], whose naturality
   square (`naturality`) commutes by `refl`; `reduct` precomposes this family into an
   algebra's structure map.
+  An adjunction carries two natural families, its `unit` and `counit`
   ([Setoid.Categories.Adjunction][]), each with its naturality square recorded as a
   field.

This record packages the pattern once, so that constructions which *consume* a natural
transformation whole — the [`Monad`][Setoid.Categories.Monad] record of M4-5e is the
inaugural consumer — can take one argument instead of a component family and a square.
Where a componentwise rendering already is the canonical form (the `Adjunction` fields,
the `⟦_⟧` family), it stays canonical; this record is the bundled view, not a
replacement.  (`Adjunction` derives `unitNT` / `counitNT` views for free.)

As with the rest of the layer (ADR-006), the record is minimal and self-contained — no
`agda-categories` dependency — and every law is stated against the target category's
hom-equality field `_≈_`, so categories with pointwise hom-setoids (the algebra
categories [`Alg`][Setoid.Categories.Algebra]) prove naturality pointwise, with no
function extensionality.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Categories.NaturalTransformation where

open import Agda.Primitive  using ( _⊔_ ) renaming ( Set to Type )
open import Level           using ( Level )

open import Setoid.Categories.Category using ( Category )
open import Setoid.Categories.Functor  using ( Functor )

private variable o ℓ e o′ ℓ′ e′ : Level
```

#### The record

A `NaturalTransformation F G` consists of the component family and its naturality
square.  The components live in the target category `𝒟`, and so does the equality in
which the square commutes.

```agda
record NaturalTransformation
  {𝒞 : Category o ℓ e} {𝒟 : Category o′ ℓ′ e′}
  (F G : Functor 𝒞 𝒟) : Type (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) where
  open Category 𝒞 renaming ( Obj to Obj₀ ; Hom to Hom₀ )
  open Category 𝒟 renaming ( Hom to Hom₁ ; _≈_ to _≈₁_ ; _∘_ to _∘₁_ )
  open Functor F renaming ( F₀ to F₀ ; F₁ to F₁ )
  open Functor G renaming ( F₀ to G₀ ; F₁ to G₁ )

  field
    -- One 𝒟-morphism per 𝒞-object: the A-th component F₀ A ⟶ G₀ A.
    component : (A : Obj₀) → Hom₁ (F₀ A) (G₀ A)

    -- The naturality square: the components commute with the image of
    -- every 𝒞-morphism, in 𝒟's hom-equality.
    natural : {A B : Obj₀} (f : Hom₀ A B)
            → component B ∘₁ F₁ f ≈₁ G₁ f ∘₁ component A
```

A small dictionary for readers coming from the classical literature: what is written
`η : F ⟹ G` with components `η_A` and square `η_B ∘ F f = G f ∘ η_A` appears here as
`η : NaturalTransformation F G` with `component η A` and `natural η f`.  Vertical and
horizontal composition of natural transformations are *not* defined yet; per the
library's two-consumer rule they will be added when a second construction needs them
(the [`Monad`][Setoid.Categories.Monad] laws below need only the components, which is
also why the monad laws there are stated componentwise).

--------------------------------------

{% include UALib.Links.md %}
