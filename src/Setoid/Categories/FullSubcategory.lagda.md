---
layout: default
file: "src/Setoid/Categories/FullSubcategory.lagda.md"
title: "Setoid.Categories.FullSubcategory module"
date: "2026-06-10"
author: "the agda-algebras development team"
---

### Full subcategories on an object predicate

This is the [Setoid.Categories.FullSubcategory][] module of the [Agda Universal Algebra Library][].

`FullSubcategory 𝐂 P` is the full subcategory of `𝐂` whose objects are the
inhabitants of `Σ (Obj 𝐂) P` — an object of `𝐂` together with evidence that it
satisfies `P` — and whose morphisms, hom-equality, identity, composition, and laws
are inherited from `𝐂` unchanged.

This is exactly the shape of the theory-satisfying classical structures
(`Semigroup α ρ = Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ Th-Semigroup`, and likewise `Monoid`,
`Group`, etc.).  Each is a full subcategory of the algebra category
[`Alg`][Setoid.Categories.Algebra] of its signature, because a homomorphism
between theory-satisfying algebras is just a homomorphism of the underlying
algebras; satisfaction of laws is a property of the objects, not structure
on the morphisms.

<!--
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
-->

#### The full subcategory

```agda
module _ (𝐂 : Category o ℓ e) where
  open Category 𝐂

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

`FullSubcategoryF`{.AgdaFunction} restricts a functor along the full-subcategory
construction.  Given `F : Functor 𝐂 𝐃` and predicates `P` on the objects of `𝐂`
and `Q` on the objects of `𝐃`, the only new data required is a *transfer* proof
that `F` sends `P`-objects to `Q`-objects.  On objects the restricted functor
pairs `F₀`{.AgdaField} with that proof; on morphisms, on morphism equalities, and
on the identity and composition laws it is literally `F`, because a full
subcategory has exactly the morphisms of its ambient category.

```agda
open Category using (Obj)
module _
  {𝐂 : Category o ℓ e} {𝐃 : Category o′ ℓ′ e′}
  {P : Obj 𝐂 → Type p} {Q : Obj 𝐃 → Type q}
  (F : Functor 𝐂 𝐃)
  where
  open Functor F

  FullSubcategoryF :
    (transfer : {A : Obj 𝐂} → P A → Q (F₀ A))
    → Functor (FullSubcategory 𝐂 P) (FullSubcategory 𝐃 Q)
  FullSubcategoryF transfer =
    record  { F₀            = λ A → ( F₀ (proj₁ A) , transfer (proj₂ A) )
            ; F₁            = F₁
            ; F-resp-≈      = F-resp-≈
            ; identity      = identity
            ; homomorphism  = homomorphism
            }
```
