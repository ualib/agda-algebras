---
layout: default
file: "src/Setoid/Categories/Category.lagda.md"
title: "Setoid.Categories.Category module"
date: "2026-06-08"
author: "the agda-algebras development team"
---

### A minimal category with a hom-setoid

This is the [Setoid.Categories.Category][] module of the [Agda Universal Algebra Library][].

`Category o ℓ e` is a self-contained, `agda-categories`-free category record (ADR-006): objects
in `Type o`, hom-types in `Type ℓ`, and a per-hom-set *equivalence* `_≈_` valued in `Type e`.
Carrying `_≈_` as a field — rather than fixing it to `_≡_` — is what lets the category of
algebras (M4-5c) use *pointwise* homomorphism equality, which `_≡_` cannot express under
`--safe` (it would need funext); the signature category `Sig` would instead instantiate
`_≈_ = _≡_`.

The record is deliberately minimal — exactly the data and laws the M4-5c–e layer needs — and
is pure `Type`-level category theory (no `Setoid` import).  It lives under `Setoid.Categories`
because its first consumers are setoid-level.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Categories.Category where

open import Agda.Primitive  using ( _⊔_ ; lsuc ) renaming ( Set to Type )
open import Level           using ( Level )
open import Relation.Binary using ( IsEquivalence )

private variable o ℓ e : Level

record Category (o ℓ e : Level) : Type (lsuc (o ⊔ ℓ ⊔ e)) where
  infixr 9 _∘_
  infix  4 _≈_
  field
    Obj : Type o
    _⇒_ : Obj → Obj → Type ℓ
    _≈_ : {A B : Obj} → (A ⇒ B) → (A ⇒ B) → Type e
    id  : {A : Obj} → A ⇒ A
    _∘_ : {A B C : Obj} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

    ≈-equiv   : {A B : Obj} → IsEquivalence (_≈_ {A} {B})
    assoc     : {A B C D : Obj} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D}
              → ((h ∘ g) ∘ f) ≈ (h ∘ (g ∘ f))
    identityˡ : {A B : Obj} {f : A ⇒ B} → (id ∘ f) ≈ f
    identityʳ : {A B : Obj} {f : A ⇒ B} → (f ∘ id) ≈ f
    ∘-resp-≈  : {A B C : Obj} {f g : B ⇒ C} {h i : A ⇒ B}
              → f ≈ g → h ≈ i → (f ∘ h) ≈ (g ∘ i)

  -- Reflexivity, symmetry, and transitivity of each hom-set's equivalence,
  -- surfaced for use in functor-law and instance proofs.
  ≈-refl  : {A B : Obj} {f : A ⇒ B} → f ≈ f
  ≈-refl  = IsEquivalence.refl ≈-equiv
  ≈-sym   : {A B : Obj} {f g : A ⇒ B} → f ≈ g → g ≈ f
  ≈-sym   = IsEquivalence.sym ≈-equiv
  ≈-trans : {A B : Obj} {f g h : A ⇒ B} → f ≈ g → g ≈ h → f ≈ h
  ≈-trans = IsEquivalence.trans ≈-equiv
```

--------------------------------------

{% include UALib.Links.md %}
