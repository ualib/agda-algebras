---
layout: default
file: "src/Setoid/Categories/Category.lagda.md"
title: "Setoid.Categories.Category module"
date: "2026-06-08"
author: "the agda-algebras development team"
---

### A minimal category with a hom-setoid

This is the [Setoid.Categories.Category][] module of the [Agda Universal Algebra Library][].

`Category o ℓ e` is a self-contained, `agda-categories`-free category record: objects
in `Type o`, hom types in `Type ℓ`, and a per-hom-set *equivalence* `_≈_` valued in
`Type e`.

Carrying `_≈_` as a field — rather than fixing it to `_≡_` — is what lets the
category of algebras use *pointwise* homomorphism equality, which `_≡_` cannot
express under `--safe` without funext.

The record is deliberately minimal — exactly the data and laws we need to express
reducts as functors — and is pure `Type`-level category theory (no `Setoid` import).
It lives under `Setoid.Categories` because its current consumers are setoid-based.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Categories.Category where

open import Agda.Primitive  using ( _⊔_ ; lsuc ) renaming ( Set to Type )
open import Level           using ( Level )
open import Relation.Binary using ( IsEquivalence )

private variable o ℓ e : Level

record Category (o ℓ e : Level) : Type (lsuc (o ⊔ ℓ ⊔ e)) where
  infixr 9 _∘_
  infix 4 _≈_

  field
    Obj  : Type o
    Hom  : Obj → Obj → Type ℓ
    _≈_  : {A B : Obj} → Hom A B → Hom A B → Type e
    id   : {A : Obj} → Hom A A
    _∘_  : {A B C : Obj} → Hom B C → Hom A B → Hom A C

    ≈-equiv    : {A B : Obj} → IsEquivalence (_≈_ {A} {B})
    assoc      : {A B C D : Obj} {f : Hom A B} {g : Hom B C} {h : Hom C D}
               → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
    identityˡ  : {A B : Obj} {f : Hom A B} → id ∘ f ≈ f
    identityʳ  : {A B : Obj} {f : Hom A B} → f ∘ id ≈ f
    ∘-resp-≈   : {A B C : Obj} {f g : Hom B C} {h i : Hom A B}
               → f ≈ g → h ≈ i → f ∘ h ≈ g ∘ i

  -- Reflexivity, symmetry, and transitivity of each hom-set's equivalence,
  -- surfaced for use in functor-law and instance proofs.
  ≈-refl  : {A B : Obj} {f : Hom A B} → f ≈ f
  ≈-refl  = IsEquivalence.refl ≈-equiv
  ≈-sym   : {A B : Obj} {f g : Hom A B} → f ≈ g → g ≈ f
  ≈-sym   = IsEquivalence.sym ≈-equiv
  ≈-trans : {A B : Obj} {f g h : Hom A B} → f ≈ g → g ≈ h → f ≈ h
  ≈-trans = IsEquivalence.trans ≈-equiv
```

--------------------------------------

{% include UALib.Links.md %}
