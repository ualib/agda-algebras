---
layout: default
file: "src/Setoid/Signatures/Functor.lagda.md"
title: "Setoid.Signatures.Functor module"
date: "2026-06-07"
author: "the agda-algebras development team"
---

### The polynomial functor `⟨_⟩` and the natural transformations of signature morphisms

This is the [Setoid.Signatures.Functor][] module of the [Agda Universal Algebra Library][].

The signature-to-setoid lifting `⟨ 𝑆 ⟩`{.AgdaFunction} ([Setoid.Signatures][]) is the
polynomial (container) functor `P_𝑆` of the signature `𝑆`.  This module makes that explicit:
`⟨ 𝑆 ⟩` is *functorial in the carrier* (`map`{.AgdaFunction}), and a
[`SigMorphism`][Overture.Signatures.Morphisms] `(ι , κ)` induces a *natural transformation*
`⟦ φ ⟧ : ⟨ 𝑆₁ ⟩ ⟹ ⟨ 𝑆₂ ⟩` whose component at a setoid `A` sends `(o , args)` to
`(ι o , args ∘ κ o)` — exactly the data that `reduct` precomposes into `Interp`.  Finally,
`⟦_⟧`{.AgdaFunction} is itself functorial: it sends `id-morphism` to the identity natural
transformation and `ψ ∘ₛ φ` to the vertical composite.

Each coherence is proved in its **strongest `--safe` form first** — propositional equality of
the *underlying functions* (`refl`), since the functor action is post-composition on the
position function, so the laws reduce to `∘`-associativity and `id`-cancellation by η.  The
directly-usable **pointwise corollary** (`… ⟨$⟩ x ≡ …`, the shape the algebra-level laws of
M4-5c will take with `≈`) then follows in one line by `cong-app`.  Equating the `Func`s
*themselves* (their `cong` proof fields) would still need funext; the underlying-function
equality is the strongest statement `--safe` allows.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Signatures.Functor where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive  using ()             renaming ( Set to Type )
open import Data.Product    using ( _,_ )
open import Function        using ( _∘_ ; Func ; id )
open import Level           using ( Level )
open import Relation.Binary using ( Setoid )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; cong-app )

import Function.Construct.Identity     as IdF
import Function.Construct.Composition  as CompF

open Func    renaming ( to to _⟨$⟩_ ; cong to ≈cong )
open Setoid  using ( Carrier )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Signatures.Morphisms  using ( SigMorphism ; ι ; κ ; id-morphism ; _∘ₛ_ )
open import Setoid.Signatures              using ( ⟨_⟩ )

private variable
  α ρ αᵇ ρᵇ αᶜ ρᶜ : Level
  𝑆 𝑆₁ 𝑆₂ 𝑆₃ : Signature 𝓞 𝓥
  A : Setoid α ρ
  B : Setoid αᵇ ρᵇ
  C : Setoid αᶜ ρᶜ
```

#### `⟨ 𝑆 ⟩` is functorial in the carrier

The action of `⟨ 𝑆 ⟩` on a setoid map `h : A ⟶ B` post-composes `h` onto the position
function, leaving the operation symbol fixed.

```agda
map : Func A B → Func (⟨ 𝑆 ⟩ A) (⟨ 𝑆 ⟩ B)
map h ⟨$⟩ (f , args)                       = f , λ i → h ⟨$⟩ args i
map h .≈cong {f , u} {.f , v} (refl , u≈v) = refl , λ i → ≈cong h (u≈v i)
```

`map` preserves identities and composition.  Each law is proved first in its strict
underlying-function form (`refl`); the pointwise corollary (suffix `-ptw`) is one `cong-app`.

```agda
map-id : (λ (x : Carrier (⟨ 𝑆 ⟩ A)) → map (IdF.function A) ⟨$⟩ x) ≡ id
map-id = refl

map-id-ptw : (x : Carrier (⟨ 𝑆 ⟩ A)) → map (IdF.function A) ⟨$⟩ x ≡ x
map-id-ptw {𝑆 = 𝑆} {A = A} x = cong-app (map-id {𝑆 = 𝑆} {A = A}) x

map-∘ : (h : Func A B) (g : Func B C)
      → (λ (x : Carrier (⟨ 𝑆 ⟩ A)) → map (CompF.function h g) ⟨$⟩ x)
        ≡ (λ x → map g ⟨$⟩ (map h ⟨$⟩ x))
map-∘ h g = refl

map-∘-ptw : (h : Func A B) (g : Func B C) (x : Carrier (⟨ 𝑆 ⟩ A))
          → map (CompF.function h g) ⟨$⟩ x ≡ map g ⟨$⟩ (map h ⟨$⟩ x)
map-∘-ptw h g x = cong-app (map-∘ h g) x
```

#### The natural transformation induced by a signature morphism

`⟦ φ ⟧ A` is the component at `A` of the natural transformation `⟨ 𝑆₁ ⟩ ⟹ ⟨ 𝑆₂ ⟩` induced
by `φ : SigMorphism 𝑆₁ 𝑆₂`: it relabels the operation symbol by `ι φ` and reindexes the
positions by `κ φ`.

```agda
⟦_⟧ : SigMorphism 𝑆₁ 𝑆₂ → (A : Setoid α ρ) → Func (⟨ 𝑆₁ ⟩ A) (⟨ 𝑆₂ ⟩ A)
⟦ φ ⟧ A ⟨$⟩ (o , args)                       = ι φ o , args ∘ κ φ o
⟦ φ ⟧ A .≈cong {o , u} {.o , v} (refl , u≈v) = refl , λ i → u≈v (κ φ o i)
```

##### Naturality

Post-composing along `h` and relabelling by `φ` commute.

```agda
naturality : {𝑆₁ 𝑆₂ : Signature 𝓞 𝓥} (φ : SigMorphism 𝑆₁ 𝑆₂) (h : Func A B)
           → (λ (x : Carrier (⟨ 𝑆₁ ⟩ A)) → map h ⟨$⟩ (⟦ φ ⟧ A ⟨$⟩ x))
             ≡ (λ x → ⟦ φ ⟧ B ⟨$⟩ (map h ⟨$⟩ x))
naturality φ h = refl

naturality-ptw : {𝑆₁ 𝑆₂ : Signature 𝓞 𝓥} (φ : SigMorphism 𝑆₁ 𝑆₂) (h : Func A B)
                 (x : Carrier (⟨ 𝑆₁ ⟩ A))
               → map h ⟨$⟩ (⟦ φ ⟧ A ⟨$⟩ x) ≡ ⟦ φ ⟧ B ⟨$⟩ (map h ⟨$⟩ x)
naturality-ptw φ h x = cong-app (naturality φ h) x
```

##### `⟦_⟧` is functorial

`⟦_⟧` sends the identity signature morphism to the identity natural transformation and a
composite morphism to the vertical composite of natural transformations.

```agda
⟦id⟧ : (λ (x : Carrier (⟨ 𝑆 ⟩ A)) → ⟦ id-morphism ⟧ A ⟨$⟩ x) ≡ id
⟦id⟧ = refl

⟦id⟧-ptw : (x : Carrier (⟨ 𝑆 ⟩ A)) → ⟦ id-morphism ⟧ A ⟨$⟩ x ≡ x
⟦id⟧-ptw {𝑆 = 𝑆} {A = A} x = cong-app (⟦id⟧ {𝑆 = 𝑆} {A = A}) x

⟦∘⟧ : {𝑆₁ 𝑆₂ 𝑆₃ : Signature 𝓞 𝓥} (φ : SigMorphism 𝑆₁ 𝑆₂) (ψ : SigMorphism 𝑆₂ 𝑆₃)
    → (λ (x : Carrier (⟨ 𝑆₁ ⟩ A)) → ⟦ ψ ∘ₛ φ ⟧ A ⟨$⟩ x)
      ≡ (λ x → ⟦ ψ ⟧ A ⟨$⟩ (⟦ φ ⟧ A ⟨$⟩ x))
⟦∘⟧ φ ψ = refl

⟦∘⟧-ptw : {𝑆₁ 𝑆₂ 𝑆₃ : Signature 𝓞 𝓥} (φ : SigMorphism 𝑆₁ 𝑆₂) (ψ : SigMorphism 𝑆₂ 𝑆₃)
          (x : Carrier (⟨ 𝑆₁ ⟩ A))
        → ⟦ ψ ∘ₛ φ ⟧ A ⟨$⟩ x ≡ ⟦ ψ ⟧ A ⟨$⟩ (⟦ φ ⟧ A ⟨$⟩ x)
⟦∘⟧-ptw {A = A} φ ψ x = cong-app (⟦∘⟧ {A = A} φ ψ) x
```

--------------------------------------

{% include UALib.Links.md %}
