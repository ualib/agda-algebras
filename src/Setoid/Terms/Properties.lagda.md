---
layout: default
title : "Setoid.Terms.Properties module (The Agda Universal Algebra Library)"
date : "2021-09-18"
author: "agda-algebras development team"
---

#### Basic properties of terms on setoids

This is the [Setoid.Terms.Properties][] module of the [Agda Universal Algebra Library][].


```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Terms.Properties {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive   using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -------------------------------------
open import Data.Product                           using ( _,_ )
open import Function.Bundles                       using () renaming ( Func to _⟶_ )
open import Function.Base                          using ( _∘_ )
open import Level                                  using ( Level )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( setoid; cong; refl)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture                       using ( proj₁ ; proj₂ )
open import Overture.Terms        {𝑆 = 𝑆}  using  ( Term )
open import Setoid.Algebras       {𝑆 = 𝑆}  using  ( Algebra ; 𝕌[_] ; 𝔻[_] ; _^_ )
open import Setoid.Functions               using  ( Img_∋_ ; eq ; isSurj ; IsSurjective
                                                  ; isSurj→IsSurjective )
open import Setoid.Homomorphisms  {𝑆 = 𝑆}  using  ( hom ; compatible-map ; IsHom ; ⊙-hom )
open import Setoid.Terms.Basic    {𝑆 = 𝑆}  using  ( 𝑻 ; _≐_  ; ≐-isRefl )

open Term
open _⟶_ using ( ) renaming ( to to _⟨$⟩_ ; cong to ≈cong )

private variable
 α ρᵃ β ρᵇ ρ χ : Level
 X : Type χ
```

The term algebra `𝑻 X` is *absolutely free* (or *universal*, or *initial*) for
algebras in the signature `𝑆`. That is, for every 𝑆-algebra `𝑨`, the following hold.

1. Every function from `𝑋` to `𝕌[ 𝑨 ]` lifts to a homomorphism from `𝑻 X` to `𝑨`.
2. The homomorphism that exists by item 1 is unique.

We now prove this in [Agda][], starting with the fact that every map from `X` to
`𝕌[ 𝑨 ]` lifts to a map from `𝕌[ 𝑻 X ]` to `𝕌[ 𝑨 ]` in a natural way, by induction
on the structure of the given term.

```agda
module _ {𝑨 : Algebra α ρ}(h : X → 𝕌[ 𝑨 ]) where
  open Algebra 𝑨      using ( Interp )                   renaming ( Domain to A )
  open Setoid A       using ( _≈_ ; reflexive )  renaming ()
  open Algebra (𝑻 X)  using ()                           renaming ( Domain to TX )

  free-lift : 𝕌[ 𝑻 X ] → 𝕌[ 𝑨 ]
  free-lift (ℊ x) = h x
  free-lift (node f t) = (f ^ 𝑨) (λ i → free-lift (t i))

  free-lift-of-surj-isSurj :
    isSurj{𝑨 = setoid X}{𝑩 = A} h → isSurj{𝑨 = TX}{𝑩 = A} free-lift
  free-lift-of-surj-isSurj hE {y} = mp p
    where
    p : Img h ∋ y
    p = hE
    mp : Img h ∋ y → Img free-lift ∋ y
    mp (eq a x) = eq (ℊ a) x

  free-lift-func : TX ⟶ A
  free-lift-func ⟨$⟩ x = free-lift x
  free-lift-func .≈cong = flcong
    where
    open _≐_
    flcong : ∀ {s t} → s ≐ t →  free-lift s ≈ free-lift t
    flcong (rfl x≡y) = reflexive (cong h x≡y)
    flcong (gnl s≐t) = ≈cong Interp (refl , flcong ∘ s≐t)
```

Naturally, at the base step of the induction, when the term has the form `generator`
x, the free lift of `h` agrees with `h`.  For the inductive step, when the given term
has the form `node f t`, the free lift is defined as follows: Assuming (the induction
hypothesis) that we know the image of each subterm `t i` under the free lift of `h`,
define the free lift at the full term by applying `f ^ 𝑨` to the images of the subterms.

The free lift so defined is a homomorphism by construction. Indeed, here is the trivial proof.

```agda
  lift-hom : hom (𝑻 X) 𝑨
  lift-hom = free-lift-func , hhom
    where
    hfunc : TX ⟶ A
    hfunc = free-lift-func

    hcomp : compatible-map (𝑻 X) 𝑨 free-lift-func
    hcomp {f}{a} = ≈cong Interp (refl , (λ i → (≈cong free-lift-func){a i} ≐-isRefl))

    hhom : IsHom (𝑻 X) 𝑨 hfunc
    hhom = record { compatible = λ{f}{a} → hcomp{f}{a} }
```

If we further assume that each of the mappings from `X` to `𝕌[ 𝑨 ]` is *surjective*,
then the homomorphisms constructed with `free-lift` and `lift-hom` are
*epimorphisms*, as we now prove.

```agda
  lift-of-epi-is-epi : isSurj{𝑨 = setoid X}{𝑩 = A} h → IsSurjective free-lift-func
  lift-of-epi-is-epi hE = isSurj→IsSurjective free-lift-func (free-lift-of-surj-isSurj hE)
```

Finally, we prove that the homomorphism is unique.  Recall, when we proved this in the module
[Basic.Terms.Properties][], we needed function extensionality. Here, by using setoid equality,
we can omit the `swelldef` hypothesis we needed previously to prove `free-unique`.


```agda
module _ {𝑨 : Algebra α ρ}{gh hh : hom (𝑻 X) 𝑨} where
  open Algebra 𝑨      using ( Interp )  renaming ( Domain to A )
  open Setoid A       using ( _≈_ )
  open Algebra (𝑻 X)  using ()          renaming ( Domain to TX )
  open SetoidReasoning A
  open _≐_
  open IsHom

  private
    g h : TX ⟶ A
    g = proj₁ gh
    h = proj₁ hh
  free-unique : (∀ x → g ⟨$⟩ (ℊ x) ≈ h ⟨$⟩ (ℊ x)) → ∀ (t : Term X) →  g ⟨$⟩ t ≈ h ⟨$⟩ t
  free-unique p (ℊ x) = p x
  free-unique p (node f t) = begin
    g ⟨$⟩ (node f t)              ≈⟨ compatible (proj₂ gh) ⟩
    (f ^ 𝑨)(λ i → (g ⟨$⟩ (t i)))  ≈⟨ ≈cong Interp (refl , λ i → free-unique p (t i)) ⟩
    (f ^ 𝑨)(λ i → (h ⟨$⟩ (t i)))  ≈˘⟨ compatible (proj₂ hh) ⟩
    h ⟨$⟩ (node f t)              ∎
```


##### Naturality of the free lift

Existence (`lift-hom`) and uniqueness (`free-unique`) together say that `𝑻 X` is a
*free* (initial) object, and freeness always brings a third, slightly less quotable
property: the assignment "generator map ↦ induced homomorphism" is *natural* in the
target algebra.  Concretely, lifting `η : X → 𝕌[ 𝑨 ]` into `𝑨` and then applying a
homomorphism `h : 𝑨 ⟶ 𝑩` is the same as lifting the composite map `h ∘ η` into `𝑩`
directly:

```text
                  lift-hom η
        𝑻 X ────────────────────→ 𝑨
            ╲                     │
             ╲                    │ h
   lift-hom   ╲                   │
   (h ∘ η)     ↘                  ↓
                                  𝑩
```

The proof is a one-liner, and *that* is the point: both routes around the triangle
are homomorphisms `𝑻 X ⟶ 𝑩` that agree on the generators (both send `ℊ x` to
`h (η x)`, definitionally), so `free-unique` forces them to agree on every term.  No
induction over terms appears here — it is already packaged inside `free-unique`.
This is the way category theory pays rent: theorems about *all* terms become
theorems about *generators only*.

(The same fact in environment form — `h (⟦ t ⟧ a) ≈ ⟦ t ⟧ (h ∘ a)` — is
`comm-hom-term` in [Setoid.Terms.Operations][], proved there by direct induction;
`free-lift-interp`, also in that module, mediates between the two phrasings.  The
companion naturality in the *signature* argument, where the algebra is fixed and the
signature varies along a morphism, is `reduct-interp` in
[Setoid.Varieties.Invariance][].)

```agda
module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}(h : hom 𝑨 𝑩)(η : X → 𝕌[ 𝑨 ]) where
 open Setoid 𝔻[ 𝑩 ] using () renaming ( _≈_ to _≈ᵇ_ ; refl to reflᵇ )

 free-lift-natural : (t : Term X)
  →                  proj₁ h ⟨$⟩ free-lift{𝑨 = 𝑨} η t ≈ᵇ free-lift{𝑨 = 𝑩} (λ x → proj₁ h ⟨$⟩ η x) t

 free-lift-natural =
  free-unique {𝑨 = 𝑩} {gh = ⊙-hom (lift-hom η) h} {hh = lift-hom (λ x → proj₁ h ⟨$⟩ η x)}
   (λ _ → reflᵇ)
```


------------------------------

<span style="float:left;">[← Setoid.Terms.Basic](Setoid.Terms.Basic.html)</span>
<span style="float:right;">[Setoid.Terms.Operations →](Setoid.Terms.Operations.html)</span>

{% include UALib.Links.md %}


