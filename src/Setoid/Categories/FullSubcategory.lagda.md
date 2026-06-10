---
layout: default
file: "src/Setoid/Categories/FullSubcategory.lagda.md"
title: "Setoid.Categories.FullSubcategory module"
date: "2026-06-10"
author: "the agda-algebras development team"
---

### Full subcategories on an object predicate

This is the [Setoid.Categories.FullSubcategory][] module of the [Agda Universal Algebra Library][].

`FullSubcategory 𝒞 P` is the full subcategory of `𝒞` whose objects are the inhabitants of
`Σ (Obj 𝒞) P` — an object of `𝒞` together with evidence that it satisfies `P` — and
whose morphisms, hom-equality, identity, composition, and laws are inherited from `𝒞`
unchanged.  This is exactly the shape of the theory-satisfying classical structures
(`Semigroup α ρ = Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ Th-Semigroup`, and likewise `Monoid`,
`Group`, …); each is a full subcategory of the algebra category
[`Alg`][Setoid.Categories.Algebra] of its signature, because a homomorphism between
theory-satisfying algebras is just a homomorphism of the underlying algebras —
satisfaction is a *property* of the objects, not structure on the morphisms.

`FullSubcategoryF` restricts a functor along such predicates; given `F : 𝒞 ⟶ 𝒟` and a
`transfer` of evidence `P A → Q (F₀ A)`, the functor maps the full subcategory on `P`
to the one on `Q`, acting as `F` on morphisms.  The functor laws are inherited
verbatim, since the hom-equalities are.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Categories.FullSubcategory where

open import Agda.Primitive              using ( _⊔_ ) renaming ( Set to Type )
open import Data.Product                using ( Σ ; _,_ ; proj₁ ; proj₂ )
open import Level                       using ( Level )
open import Setoid.Categories.Category  using ( Category )
open import Setoid.Categories.Functor   using ( Functor )

private variable o ℓ e o′ ℓ′ e′ p q : Level
```

#### The full subcategory

```agda
module _ (𝒞 : Category o ℓ e) where
  open Category 𝒞

  FullSubcategory : (P : Obj → Type p) → Category (o ⊔ p) ℓ e
  FullSubcategory P = record
    { Obj        = Σ Obj P
    ; Hom        = λ (A B : Σ Obj P) → Hom (proj₁ A) (proj₁ B)
    ; _≈_        = _≈_
    ; id         = id
    ; _∘_        = _∘_
    ; ≈-equiv    = ≈-equiv
    ; assoc      = assoc
    ; identityˡ  = identityˡ
    ; identityʳ  = identityʳ
    ; ∘-resp-≈   = ∘-resp-≈
    }
```

#### Restricting a functor to a full subcategory

```agda
open Category
module _
  {𝒞 : Category o ℓ e} {𝒟 : Category o′ ℓ′ e′}
  {P : Obj 𝒞 → Type p} {Q : Obj 𝒟 → Type q}
  (F : Functor 𝒞 𝒟)
  where
  open Functor F

  FullSubcategoryF :
    (transfer : {A : Obj 𝒞} → P A → Q (F₀ A))
    → Functor (FullSubcategory 𝒞 P) (FullSubcategory 𝒟 Q)
  FullSubcategoryF transfer = record
    { F₀            = λ A → ( F₀ (proj₁ A) , transfer (proj₂ A) )
    ; F₁            = F₁
    ; F-resp-≈      = F-resp-≈
    ; identity      = identity
    ; homomorphism  = homomorphism
    }
```

--------------------------------------

{% include UALib.Links.md %}
