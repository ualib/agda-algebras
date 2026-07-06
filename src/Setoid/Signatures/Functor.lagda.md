---
layout: default
file: "src/Setoid/Signatures/Functor.lagda.md"
title: "Setoid.Signatures.Functor module"
date: "2026-06-07"
author: "the agda-algebras development team"
---

### The signature polynomial functor and natural transformations of signature morphisms

This is the [Setoid.Signatures.Functor][] module of the [Agda Universal Algebra Library][].

The signature-to-setoid lifting `⟨ 𝑆 ⟩`{.AgdaFunction} ([Setoid.Signatures][]) is the
polynomial (container) functor `P_𝑆` of the signature `𝑆`.  This module makes that
explicit: `⟨ 𝑆 ⟩` is *functorial in the carrier* (`map`{.AgdaFunction}), and a
[`SigMorphism`][Overture.Signatures.Morphisms] `(ι , κ)` induces a
*natural transformation* `⟦ φ ⟧ : ⟨ 𝑆₁ ⟩ ⟹ ⟨ 𝑆₂ ⟩` whose component at a setoid `A`
sends `(o , args)` to `(ι o , args ∘ κ o)` — exactly the data that `reduct`
precomposes into `Interp`.  Moreover, `⟦_⟧`{.AgdaFunction} is itself functorial: it
sends `id-morphism` to the identity natural transformation and `ψ ∘ₛ φ` to the
vertical composite.

Each coherence is proved in its strongest `--safe` form first — propositional equality
of the underlying functions, since the functor action is post-composition on the
position function, so the laws reduce to `∘`-associativity and `id`-cancellation by η.
The weaker, *pointwise* equality (the shape that later, algebra-level laws will take
with `≈`) follows immediately.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Signatures.Functor where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Data.Product                           using ( _,_ )
open import Function                               using ( Func ; _∘_ )
open import Function.Construct.Identity            using () renaming (function to identity)
open import Function.Construct.Composition         using () renaming (function to _∘'_ )
open import Level                                  using ( Level )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; cong-app )

open Func using (cong) renaming ( to to _⟨$⟩_ )
open Setoid using ( Carrier )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Signatures.Morphisms using ( SigMorphism ; ι ; κ ; id-morphism ; _∘ₛ_ )
open import Setoid.Signatures using ( ⟨_⟩ )

private variable
  α ρ αᵇ ρᵇ αᶜ ρᶜ : Level
```
-->

#### `⟨ 𝑆 ⟩` is functorial in the carrier

The action of `⟨ 𝑆 ⟩` on a setoid map `h : A ⟶ B` post-composes `h` onto the position
function, leaving the operation symbol fixed.

```agda
map : {S : Signature 𝓞 𝓥} {A : Setoid α ρ} {B : Setoid αᵇ ρᵇ}
  → Func A B → Func (⟨ S ⟩ A) (⟨ S ⟩ B)
map h ⟨$⟩ (f , args) = f , λ i → h ⟨$⟩ args i
map h .cong {f , u} {.f , v} (refl , u≈v) = refl , λ i → cong h (u≈v i)
```

`map` preserves identities and composition.  Each law is proved first in its strict
underlying-function form (`refl`); the pointwise corollary (suffix `-ptw`) is one `cong-app`.

```agda
module _ {S : Signature 𝓞 𝓥} {A : Setoid α ρ} where
  map-id : map (identity A) ⟨$⟩_ ≡ λ (x : Carrier (⟨ S ⟩ A)) → x
  map-id = refl

  map-id-ptw : ∀ x → map (identity A) ⟨$⟩ x ≡ x
  map-id-ptw = cong-app map-id

  module _ {B : Setoid αᵇ ρᵇ} {C : Setoid αᶜ ρᶜ} {h : Func A B} {g : Func B C} where
    map-∘ : map (h ∘' g) ⟨$⟩_ ≡ λ (x : Carrier (⟨ S ⟩ A)) → map g ⟨$⟩ (map h ⟨$⟩ x)
    map-∘ = refl

    map-∘-ptw : ∀ x → map (h ∘' g) ⟨$⟩ x ≡ map g ⟨$⟩ (map h ⟨$⟩ x)
    map-∘-ptw = cong-app map-∘
```

#### The natural transformation induced by a signature morphism

`⟦ φ ⟧ A` is the component at `A` of the natural transformation `⟨ 𝑆₁ ⟩ ⟹ ⟨ 𝑆₂ ⟩` induced
by `φ : SigMorphism 𝑆₁ 𝑆₂`: it relabels the operation symbol by `ι φ` and reindexes the
positions by `κ φ`.

```agda
⟦_⟧ : {𝑆₁ 𝑆₂ : Signature 𝓞 𝓥} → SigMorphism 𝑆₁ 𝑆₂
  → (A : Setoid α ρ) → Func (⟨ 𝑆₁ ⟩ A) (⟨ 𝑆₂ ⟩ A)
⟦ φ ⟧ A ⟨$⟩ (o , args) = ι φ o , λ i → args (κ φ o i)
⟦ φ ⟧ A .cong {o , u} {.o , v} (refl , u≈v) = refl , λ i → u≈v (κ φ o i)
```

##### Naturality

Post-composing along `h` and relabelling by `φ` commute.

```agda
module _
  {𝑆₁ 𝑆₂ : Signature 𝓞 𝓥}
  {A : Setoid α ρ}
  {B : Setoid αᵇ ρᵇ}
  {φ : SigMorphism 𝑆₁ 𝑆₂}
  {h : Func A B}
  where

  naturality : map h ⟨$⟩_ ∘ ⟦ φ ⟧ A ⟨$⟩_ ≡ ⟦ φ ⟧ B ⟨$⟩_ ∘ map h ⟨$⟩_
  naturality = refl

  naturality-ptw : ∀ x → map h ⟨$⟩ (⟦ φ ⟧ A ⟨$⟩ x) ≡ ⟦ φ ⟧ B ⟨$⟩ (map h ⟨$⟩ x)
  naturality-ptw = cong-app naturality
```

##### Functoriality of `⟦_⟧`

`⟦_⟧` sends the identity signature morphism to the identity natural transformation and a
composite morphism to the vertical composite of natural transformations.

```agda
module _ {S : Signature 𝓞 𝓥} {A : Setoid α ρ} where
  ⟦id⟧ : ⟦ id-morphism ⟧ A ⟨$⟩_ ≡ λ (x : Carrier (⟨ S ⟩ A)) → x
  ⟦id⟧ = refl

  ⟦id⟧-ptw : ∀ x → ⟦ id-morphism ⟧ A ⟨$⟩ x ≡ x
  ⟦id⟧-ptw = cong-app ⟦id⟧


module _
  {𝑆₁ 𝑆₂ 𝑆₃ : Signature 𝓞 𝓥}
  {A : Setoid α ρ}
  {φ : SigMorphism 𝑆₁ 𝑆₂}
  {ψ : SigMorphism 𝑆₂ 𝑆₃}
  where
  ⟦∘⟧ : ⟦ ψ ∘ₛ φ ⟧ A ⟨$⟩_ ≡ ⟦ ψ ⟧ A ⟨$⟩_ ∘ ⟦ φ ⟧ A ⟨$⟩_
  ⟦∘⟧ = refl

  ⟦∘⟧-ptw : ∀ x → ⟦ ψ ∘ₛ φ ⟧ A ⟨$⟩ x ≡ ⟦ ψ ⟧ A ⟨$⟩ (⟦ φ ⟧ A ⟨$⟩ x)
  ⟦∘⟧-ptw = cong-app ⟦∘⟧
```
