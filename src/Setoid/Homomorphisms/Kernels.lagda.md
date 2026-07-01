---
layout: default
title : "Setoid.Homomorphisms.Kernels module (Agda Universal Algebra Library)"
date : "2021-09-13"
author: "agda-algebras development team"
---

#### Kernels of Homomorphisms

This is the [Setoid.Homomorphisms.Kernels][] module of the [Agda Universal Algebra Library][].

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Homomorphisms.Kernels where

-- Imports from Agda and the Agda Standard Library ------------------------------------------
open  import Data.Product                           using ( _,_ ;  proj₁ ; proj₂ )
open  import Function   renaming ( Func to _⟶_ )    using ( _∘_ ; id )
open  import Level                                  using ( Level )
open  import Relation.Binary                        using ( Setoid )
open  import Relation.Binary.PropositionalEquality  using (refl)

-- Imports from the Agda Universal Algebra Library ------------------------------------------
open  import Overture                    using ( kerRel ; kerRelOfEquiv ; 𝓞 ; 𝓥 ; Signature)
open  import Setoid.Functions            using ( Image_∋_ )
open  import Setoid.Algebras             using ( Algebra ; _^_ ; 𝔻[_] )
open  import Setoid.Congruences          using ( _∣≈_ ; Con ; mkcon ; _╱_ ; IsCongruence )
open  import Setoid.Homomorphisms.Basic  using ( hom ; IsHom ; epi ; IsEpi ; epi→hom ; 𝒾𝒹 )

private variable  α β ρᵃ ρᵇ ℓ : Level

open _⟶_ using ( cong ) renaming ( to to _⟨$⟩_ )

module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ}{𝑩 : Algebra β ρᵇ} ((hmap , hhom) : hom 𝑨 𝑩) where
  open Algebra 𝑩   using ( Interp ) renaming ( Domain to B )
  open Setoid B    using ( _≈_ ; sym ; trans ; isEquivalence )
  private h = _⟨$⟩_ hmap
```

`HomKerComp` asserts that the kernel of a homomorphism is compatible with the basic operations.
That is, if each `(u i, v i)` belongs to the kernel, then so does the pair `((f ^ 𝑨) u , (f ^ 𝑨) v)`.

```agda
  HomKerComp : 𝑨 ∣≈ kerRel _≈_ h
  HomKerComp f {u}{v} kuv = Goal
    where
    fhuv : (f ^ 𝑩)(h ∘ u) ≈ (f ^ 𝑩)(h ∘ v)
    fhuv = cong Interp (refl , kuv)

    lem1 : h ((f ^ 𝑨) u) ≈ (f ^ 𝑩)(h ∘ u)
    lem1 = IsHom.compatible hhom

    lem2 : (f ^ 𝑩) (h ∘ v) ≈ h ((f ^ 𝑨) v)
    lem2 = sym (IsHom.compatible hhom)

    Goal : h ((f ^ 𝑨) u) ≈ h ((f ^ 𝑨) v)
    Goal = trans lem1 (trans fhuv lem2)
```

The kernel of a homomorphism is a congruence of the domain, which we construct as follows.

```agda
  kercon : Con 𝑨 ρᵇ
  kercon =  kerRel _≈_ h ,
            mkcon (λ x → cong hmap x)(kerRelOfEquiv isEquivalence h)(HomKerComp)
```

Now that we have a congruence, we can construct the quotient relative to the kernel.

```agda
  kerquo : Algebra α ρᵇ
  kerquo = 𝑨 ╱ kercon

ker[_⇒_]_ :  {𝑆 : Signature 𝓞 𝓥} (𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ) (𝑩 : Algebra β ρᵇ) → hom 𝑨 𝑩 → Algebra _ _
ker[ 𝑨 ⇒ 𝑩 ] h = kerquo h
```


#### The canonical projection

Given an algebra `𝑨` and a congruence `θ`, the *canonical projection* is a map from `𝑨` onto `𝑨 ╱ θ` that is constructed, and proved epimorphic, as follows.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ}{𝑩 : Algebra β ρᵇ} (h : hom 𝑨 𝑩) where
  open IsCongruence

  πepi : (θ : Con 𝑨 ℓ) → epi 𝑨 (𝑨 ╱ θ)
  πepi θ = p , pepi
    where

    open Setoid 𝔻[ 𝑨 ╱ θ ]    using () renaming ( sym to ≈sym ; refl to ≈refl )
    open IsHom {𝑨 = (𝑨 ╱ θ)}  using ( compatible )
    open IsEpi

    p : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑨 ╱ θ ]
    p ⟨$⟩ x = x
    p .cong = reflexive (θ .proj₂)

    pepi : IsEpi 𝑨 (𝑨 ╱ θ) p
    pepi .isHom .compatible = ≈sym (𝒾𝒹 .proj₂ .compatible)
    pepi .isSurjective {y} = Image_∋_.eq y ≈refl
```

In may happen that we don't care about the surjectivity of `πepi`, in which
case would might prefer to work with the *homomorphic reduct* of `πepi`.
This is obtained by applying `epi-to-hom`, like so.

```agda
  πhom : (θ : Con 𝑨 ℓ) → hom 𝑨 (𝑨 ╱ θ)
  πhom θ = epi→hom 𝑨 (𝑨 ╱ θ) (πepi θ)
```

We combine the foregoing to define a function that takes 𝑆-algebras `𝑨` and `𝑩`,
and a homomorphism `h : hom 𝑨 𝑩` and returns the canonical epimorphism from `𝑨`
onto `𝑨 [ 𝑩 ]/ker h`. (Recall, the latter is the special notation we defined
above for the quotient of `𝑨` modulo the kernel of `h`.)

```agda
  πker : epi 𝑨 (ker[ 𝑨 ⇒ 𝑩 ] h)
  πker = πepi (kercon h)
```

The kernel of the canonical projection of `𝑨` onto `𝑨 / θ` is equal to `θ`,
but since equality of inhabitants of certain types (like `Congruence` or `Rel`)
can be a tricky business, we settle for proving the containment `𝑨 / θ ⊆ θ`.
Of the two containments, this is the easier one to prove; luckily it is also
the one we need later.

```agda
  ker-in-con : {θ : Con 𝑨 ℓ} → ∀ {x}{y} → kercon (πhom θ) .proj₁ x y →  θ .proj₁ x y
  ker-in-con = id
```
