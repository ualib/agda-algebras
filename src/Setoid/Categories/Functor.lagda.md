---
layout: default
file: "src/Setoid/Categories/Functor.lagda.md"
title: "Setoid.Categories.Functor module"
date: "2026-06-08"
author: "the agda-algebras development team"
---

### Functors between minimal categories

This is the [Setoid.Categories.Functor][] module of the [Agda Universal Algebra Library][].

A *functor* is a structure-preserving translation between categories — the
categorical analog of a homomorphism.  Where a homomorphism of algebras carries
elements to elements while preserving the operations, a `Functor 𝒞 𝒟` carries the
*objects* of `𝒞` to objects of `𝒟` (the object map `F₀`{.AgdaField}) and the
*morphisms* of `𝒞` to morphisms of `𝒟` (the hom map `F₁`{.AgdaField}), while
preserving the only structure a category has: identities and composition.  Those two
preservation conditions are the functor laws `identity`{.AgdaField} and
`homomorphism`{.AgdaField}, and — as everywhere in this layer — they are stated up to
the *target* category's hom-equality `_≈_`, so a category whose hom-equality is
pointwise can prove them pointwise, without function extensionality.

Why insist on the laws, rather than taking any pair of maps `(F₀ , F₁)`?  Because the
laws are what make diagram-chasing arguments transport along `F`: a commuting diagram
in `𝒞` is a tower of composites, and `homomorphism` is exactly the license to push
`F` through each composite, corner by corner.  The third field, `F-resp-≈`{.AgdaField},
plays the same role for equational rewriting that `cong` plays for setoid functions:
it lets a proof replace a morphism by an equal one underneath `F₁`.  (In a setting with
unique identity proofs `F-resp-≈` would be automatic; with hom-*setoids* it must be
data, just as `Func` must carry `cong`.)

The two running examples in this library are good ones to keep in mind:

+  `reductF φ` ([Classical.Categories.Reduct][]) translates the world of
   `𝑆₂`-algebras into the world of `𝑆₁`-algebras along a signature morphism `φ`: the
   object map forgets (reindexes) operations, the hom map is the identity on the
   underlying setoid maps.
+  `adjoinUnitF` ([Classical.Categories.AdjoinUnit][]) translates semigroups into
   monoids by freely adjoining a unit: the object map genuinely *constructs* (it
   enlarges the carrier), and the hom map extends a homomorphism to the new element.

This module also provides the identity functor `idF`{.AgdaFunction} and functor
composition `_∘F_`{.AgdaFunction}.  They are what make "functor" a closed vocabulary —
the composite of two translations is a translation — and they are needed the moment a
construction must *name* a composite functor, as the [`Monad`][Setoid.Categories.Monad]
record does when it types its unit `Id ⟹ T` and multiplication `T ∘ T ⟹ T`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Categories.Functor where

open import Agda.Primitive  using ( _⊔_ ) renaming ( Set to Type )
open import Level           using ( Level )

open import Setoid.Categories.Category using ( Category )

private variable
  o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ : Level

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

#### The identity functor and composition of functors

The identity functor leaves objects and morphisms untouched; its laws are each
hom-setoid's reflexivity.

```agda
idF : {𝒞 : Category o ℓ e} → Functor 𝒞 𝒞
idF {𝒞 = 𝒞} = record
  { F₀            = λ A → A
  ; F₁            = λ f → f
  ; F-resp-≈      = λ f≈g → f≈g
  ; identity      = ≈-refl
  ; homomorphism  = ≈-refl
  }
  where open Category 𝒞 using ( ≈-refl )
```

Functors compose in the application order of their object maps: `(G ∘F F)` first
applies `F`, then `G`, on objects and morphisms alike.  Each composite law unfolds to
"push the inner functor's law through the outer functor, then apply the outer
functor's law" — one `F-resp-≈` followed by one `≈-trans`, a pattern worth noticing
because every composite-functor proof in this library has this shape.

```agda
infixr 9 _∘F_

_∘F_ : {𝒞 : Category o ℓ e} {𝒟 : Category o′ ℓ′ e′} {ℰ : Category o″ ℓ″ e″}
  → Functor 𝒟 ℰ → Functor 𝒞 𝒟 → Functor 𝒞 ℰ
_∘F_ {ℰ = ℰ} G F = record
  { F₀            = λ A → G.F₀ (F.F₀ A)
  ; F₁            = λ f → G.F₁ (F.F₁ f)
  ; F-resp-≈      = λ f≈g → G.F-resp-≈ (F.F-resp-≈ f≈g)
  ; identity      = ≈-trans (G.F-resp-≈ F.identity) G.identity
  ; homomorphism  = ≈-trans (G.F-resp-≈ F.homomorphism) G.homomorphism
  }
  where
  open Category ℰ using ( ≈-trans )
  module F = Functor F
  module G = Functor G
```

--------------------------------------

{% include UALib.Links.md %}
