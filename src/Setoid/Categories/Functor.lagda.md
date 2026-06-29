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
elements to elements while preserving the operations, a `Functor 𝐂 𝐃` carries the
*objects* of `𝐂` to objects of `𝐃` (the object map `F₀`{.AgdaField}) and the
*morphisms* of `𝐂` to morphisms of `𝐃` (the hom map `F₁`{.AgdaField}), while
preserving the only structure a category has: identities and composition.  Those two
preservation conditions are the functor laws `identity`{.AgdaField} and
`homomorphism`{.AgdaField}, and — as everywhere in this layer — they are stated up to
the *target* category's hom-equality `_≈_`, so a category whose hom-equality is
pointwise can prove them pointwise, without function extensionality.

Why insist on the laws, rather than taking any pair of maps `(F₀ , F₁)`?  Because the
laws are what make diagram-chasing arguments transport along `F`: a commuting diagram
in `𝐂` is a tower of composites, and `homomorphism` is exactly the license to push
`F` through each composite, corner by corner.  The third field, `F-resp-≈`{.AgdaField},
plays the same role for equational rewriting that `cong` plays for setoid functions:
it lets a proof replace a morphism by an equal one underneath `F₁`.  (In a setting with
unique identity proofs `F-resp-≈` would be automatic; with hom-*setoids* it must be
data, just as `Func` must carry `cong`.)

The two running examples in this library are good ones to keep in mind:

+  `reductF φ` ([Setoid.Categories.Reduct][]) translates the world of
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
open import Function           using ( id )
open import Level           using ( Level )

open import Setoid.Categories.Category using ( Category )

private variable
  o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ : Level

record Functor (𝐂 : Category o ℓ e) (𝐃 : Category o′ ℓ′ e′) : Type (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  open Category 𝐂 renaming (Obj to 𝐂₀; Hom to 𝐂[_,_]; _≈_ to _≈ᵈᵒᵐ_; id to idᵈᵒᵐ; _∘_ to _∘ᵈᵒᵐ_)
  open Category 𝐃 renaming (Obj to 𝐃₀; Hom to 𝐃[_,_]; _≈_ to _≈ᶜᵒᵈ_; id to idᶜᵒᵈ; _∘_ to _∘ᶜᵒᵈ_)
  field
    F₀ : 𝐂₀ → 𝐃₀
    F₁ : {A B : 𝐂₀} → 𝐂[ A , B ] → 𝐃[ F₀ A , F₀ B ]
    F-resp-≈ : {A B : 𝐂₀} {f g : 𝐂[ A , B ]} → f ≈ᵈᵒᵐ g → F₁ f ≈ᶜᵒᵈ F₁ g
    identity : {A : 𝐂₀} → F₁ (idᵈᵒᵐ {A}) ≈ᶜᵒᵈ idᶜᵒᵈ
    homomorphism : {A B E : 𝐂₀} {f : 𝐂[ A , B ] } {g : 𝐂[ B , E ]} → F₁ (g ∘ᵈᵒᵐ f) ≈ᶜᵒᵈ F₁ g ∘ᶜᵒᵈ F₁ f
```

#### The identity functor and composition of functors

The identity functor leaves objects and morphisms untouched; its laws are each
hom-setoid's reflexivity.

```agda
idF : {𝐂 : Category o ℓ e} → Functor 𝐂 𝐂
idF {𝐂 = 𝐂} = record  { F₀            = id
                      ; F₁            = id
                      ; F-resp-≈      = id
                      ; identity      = ≈-refl
                      ; homomorphism  = ≈-refl
                      }
  where open Category 𝐂 using ( ≈-refl )
```

Functors compose in the application order of their object maps: `(G ∘F F)` first
applies `F`, then `G`, on objects and morphisms alike.  Each composite law unfolds to
"push the inner functor's law through the outer functor, then apply the outer
functor's law" — one `F-resp-≈` followed by one `≈-trans`, a pattern worth noticing
because every composite-functor proof in this library has this shape.

```agda
infixr 9 _∘F_

_∘F_ : {𝐂 : Category o ℓ e} {𝐃 : Category o′ ℓ′ e′} {𝐄 : Category o″ ℓ″ e″}
  → Functor 𝐃 𝐄 → Functor 𝐂 𝐃 → Functor 𝐂 𝐄
_∘F_ {𝐄 = 𝐄} G F = record
  { F₀            = λ A → G.F₀ (F.F₀ A)
  ; F₁            = λ f → G.F₁ (F.F₁ f)
  ; F-resp-≈      = λ f≈g → G.F-resp-≈ (F.F-resp-≈ f≈g)
  ; identity      = ≈-trans (G.F-resp-≈ F.identity) G.identity
  ; homomorphism  = ≈-trans (G.F-resp-≈ F.homomorphism) G.homomorphism
  }
  where
  open Category 𝐄 using ( ≈-trans )
  module F = Functor F
  module G = Functor G
```
