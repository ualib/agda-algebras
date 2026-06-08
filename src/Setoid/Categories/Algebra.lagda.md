---
layout: default
file: "src/Setoid/Categories/Algebra.lagda.md"
title: "Setoid.Categories.Algebra module"
date: "2026-06-08"
author: "the agda-algebras development team"
---

### The category of `𝑆`-algebras

This is the [Setoid.Categories.Algebra][] module of the [Agda Universal Algebra Library][].

`Alg 𝑆 α ρ` assembles the `𝑆`-algebras at levels `(α , ρ)` into a
[`Category`][Setoid.Categories.Category]: objects are `Algebra α ρ`, homs are the setoid
homomorphisms `hom` of [Setoid.Homomorphisms][], identity and composition are `𝒾𝒹` and
`⊙-hom`, and the hom-equality `_≋_` is **pointwise** — two homomorphisms are equal when their
underlying maps agree on every element, in the codomain's setoid equality.  This pointwise
hom-setoid is exactly what `_≡_` cannot provide under `--safe` (ADR-006), and is why the
`Category` record carries `_≈_` as a field.

The `assoc` and identity laws hold by the codomain's `refl` (the underlying maps are
definitionally equal — `⊙-hom` is function composition, `𝒾𝒹` the identity map); `∘-resp-≈`
is the one law with content, combining the codomain's `trans` with a hom's `cong`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Categories.Algebra {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive  using ( _⊔_ ; lsuc ) renaming ( Set to Type )
open import Data.Product    using ( proj₁ )
open import Function        using ( Func )
open import Level           using ( Level )
open import Relation.Binary using ( Setoid ; IsEquivalence )

open import Setoid.Algebras.Basic           {𝑆 = 𝑆} using ( Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Homomorphisms.Basic      {𝑆 = 𝑆} using ( hom )
open import Setoid.Homomorphisms.Properties {𝑆 = 𝑆} using ( ⊙-hom ; 𝒾𝒹 )
open import Setoid.Categories.Category               using ( Category )

open Func renaming ( to to _⟨$⟩_ ; cong to ≈cong )

private variable α ρ : Level
```

#### Pointwise equality of homomorphisms

```agda
_≋_ : {𝑨 𝑩 : Algebra α ρ} → hom 𝑨 𝑩 → hom 𝑨 𝑩 → Type (α ⊔ ρ)
_≋_ {𝑨 = 𝑨} {𝑩} f g = ∀ (x : 𝕌[ 𝑨 ]) → Setoid._≈_ 𝔻[ 𝑩 ] (proj₁ f ⟨$⟩ x) (proj₁ g ⟨$⟩ x)

≋-equiv : {𝑨 𝑩 : Algebra α ρ} → IsEquivalence (_≋_ {𝑨 = 𝑨} {𝑩})
≋-equiv {𝑩 = 𝑩} = record
  { refl  = λ _       → Setoid.refl  𝔻[ 𝑩 ]
  ; sym   = λ f≋g x   → Setoid.sym   𝔻[ 𝑩 ] (f≋g x)
  ; trans = λ f≋g g≋h x → Setoid.trans 𝔻[ 𝑩 ] (f≋g x) (g≋h x)
  }
```

#### The category

```agda
Alg : (α ρ : Level) → Category (𝓞 ⊔ 𝓥 ⊔ lsuc (α ⊔ ρ)) (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ) (α ⊔ ρ)
Alg α ρ = record
  { Obj       = Algebra α ρ
  ; _⇒_       = hom
  ; _≈_       = _≋_
  ; id        = 𝒾𝒹
  ; _∘_       = λ g f → ⊙-hom f g
  ; ≈-equiv   = ≋-equiv
  ; assoc     = λ {_} {_} {_} {𝑫} _ → Setoid.refl 𝔻[ 𝑫 ]
  ; identityˡ = λ {_} {𝑩} _ → Setoid.refl 𝔻[ 𝑩 ]
  ; identityʳ = λ {_} {𝑩} _ → Setoid.refl 𝔻[ 𝑩 ]
  ; ∘-resp-≈  = λ {_} {_} {𝑪} {_} {g} {h} f≋g h≋i x →
                  Setoid.trans 𝔻[ 𝑪 ] (f≋g (proj₁ h ⟨$⟩ x)) (≈cong (proj₁ g) (h≋i x))
  }
```

--------------------------------------

{% include UALib.Links.md %}
