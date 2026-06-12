---
layout: default
file: "src/Setoid/Categories/Category.lagda.md"
title: "Setoid.Categories.Category module"
date: "2026-06-08"
author: "the agda-algebras development team"
---

### A minimal category with a hom-setoid

This is the [Setoid.Categories.Category][] module of the [Agda Universal Algebra Library][].

A *category* is the simplest mathematical setting in which one can speak of objects
and of structure-preserving passages between them, without saying what the objects
are made of.  The data is: a collection of *objects*; for each pair of objects a
collection of *morphisms* (`Hom A B`, drawn as arrows `A ⟶ B`); an *identity* arrow
on every object; and a *composition* taking `g : B ⟶ C` and `f : A ⟶ B` to
`g ∘ f : A ⟶ C`.  The laws — associativity of composition and the two identity laws —
are exactly the monoid axioms, generalized to a setting where two arrows compose only
when their endpoints match.  That is the right level of generality for this library's
purposes: the categories we care about have algebras (or signatures, or setoids) as
objects and homomorphisms (or signature morphisms, or setoid functions) as arrows,
and theorems stated at the category level — functoriality, adjointness, monad laws —
then apply to all of them at once.  The reader who wants a single mental picture
should hold on to *the category of `𝑆`-algebras*: objects are algebras, arrows are
homomorphisms, composition is composition of maps
([`Alg`][Setoid.Categories.Algebra]).

`Category o ℓ e` is a self-contained, `agda-categories`-free category record: objects
in `Type o`, hom types in `Type ℓ`, and a per-hom-set *equivalence* `_≈_` valued in
`Type e`.

The one departure from the textbook definition deserves emphasis, because it is
forced by the constructive setting and recurs throughout the layer.  Classically one
says two morphisms simply *are or are not equal*; here every hom-set carries its own
equivalence relation `_≈_`, supplied as a field, and all laws are stated against it.
Carrying `_≈_` as a field — rather than fixing it to propositional `_≡_` — is what
lets the category of algebras use *pointwise* homomorphism equality ("the underlying
maps agree on every element"), which `_≡_` cannot express under `--safe` without
function extensionality.  The two instances built so far sit at the two extremes
(ADR-006): the category `Sig` of signatures uses `_≡_` and proves its laws by `refl`
([Overture.Signatures.Morphisms][]), while the category `Alg 𝑆` of algebras uses the
pointwise hom-setoid `_≋_` ([Setoid.Categories.Algebra][]).  One record accommodates
both precisely because the hom-equality is data.

The record is deliberately minimal — exactly the data and laws we need to express
reducts as functors, adjunctions, and monads — and is pure `Type`-level category
theory (no `Setoid` import).  It lives under `Setoid.Categories` because its current
consumers are setoid-based.  The rest of the vocabulary builds on it in order:
[`Functor`][Setoid.Categories.Functor] (translations between categories),
[`NaturalTransformation`][Setoid.Categories.NaturalTransformation] (comparisons
between translations), [`Adjunction`][Setoid.Categories.Adjunction] (free ⊣
forgetful pairs), and [`Monad`][Setoid.Categories.Monad] (formal-expression
structure, e.g. terms-with-substitution).

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
