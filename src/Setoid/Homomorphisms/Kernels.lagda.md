---
layout: default
title : "Setoid.Homomorphisms.Kernels module (Agda Universal Algebra Library)"
date : "2021-09-13"
author: "agda-algebras development team"
---

#### Kernels of Homomorphisms

This is the [Setoid.Homomorphisms.Kernels][] module of the [Agda Universal Algebra Library][].

The **kernel** of a homomorphism `h : hom 𝑨 𝑩` is the binary relation on the
carrier of `𝑨` that relates `a₀` and `a₁` when `h a₀` and `h a₁` are equal in `𝑩`.

It is an equivalence relation because it is the pullback of one along `h`, which is
`kerRelOfEquiv`{.AgdaFunction} of [Overture.Relations][]; what this module adds is
that it is also compatible with the basic operations, hence a congruence, so that
the quotient by the kernel is again an algebra.

`HomKerComp`{.AgdaFunction} is the compatibility proof, `kercon`{.AgdaFunction} is
the congruence, and `kerquo`{.AgdaFunction}, also written `ker[ 𝑨 ⇒ 𝑩 ] h`, is the
quotient.  The kernel is the inverse image of the diagonal of `𝑩`, and the inverse
image of any congruence of `𝑩` is again a congruence of `𝑨`
(`pullbackCon`{.AgdaFunction}).

This module also supplies the homomorphisms that go with a quotient:

+  `πepi`{.AgdaFunction} is the canonical projection of `𝑨` onto `𝑨 ╱ θ`, for any
   congruence `θ`, presented as an epimorphism;
+  `πhom`{.AgdaFunction} is its homomorphism reduct;
+  `πker`{.AgdaFunction} is the special case that projects onto a kernel quotient;
+  `ker-in-con`{.AgdaFunction} says the kernel of `πhom θ` is contained in `θ`.

Together with the congruences of [Setoid.Congruences][], these are the components
with which the first homomorphism theorem of [Setoid.Homomorphisms.Noether][] is
stated.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Setoid.Homomorphisms.Kernels where

-- Imports from Agda and the Agda Standard Library ------------------------------------------
open  import Data.Product                           using ( _,_ ;  proj₁ ; proj₂ )
open  import Function   renaming ( Func to _⟶_ )    using ( _∘_ ; id )
open  import Level                                  using ( Level )
open  import Relation.Binary                        using ( Setoid ; IsEquivalence )
open  import Relation.Binary.PropositionalEquality  using (refl)

-- Imports from the Agda Universal Algebra Library ------------------------------------------
open  import Overture                    using ( kerRel ; kerRelOfEquiv ; 𝓞 ; 𝓥 ; Signature)
open  import Setoid.Functions            using ( Image_∋_ )
open  import Setoid.Algebras             using ( Algebra ; _^_ ; 𝔻[_] )
open  import Setoid.Congruences          using ( _∣≈_ ; Con ; mkcon ; _╱_ ; IsCongruence
                                               ; reflexive ; is-equivalence ; is-compatible )
open  import Setoid.Homomorphisms.Basic  using ( hom ; IsHom ; epi ; IsEpi ; epi→hom ; 𝒾𝒹 )

private variable  α β ρᵃ ρᵇ ℓ : Level

open _⟶_ using ( cong ) renaming ( to to _⟨$⟩_ )
```
-->

```agda
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

#### The inverse image of a congruence

More generally, a homomorphism `h : 𝑨 → 𝑩` pulls every congruence `θ` of `𝑩` back
to the congruence `pullbackCon h θ`{.AgdaFunction} of `𝑨`, which relates `x` and
`y` when `h x θ h y`; the kernel is the case where `θ` is the diagonal.  It
contains the equality of `𝑨` because `h` respects equality, and it is compatible
with the operations because `h` commutes with them up to the equality of `𝑩`,
which `θ` contains.  Pulling factor pairs back along isomorphisms is how
[Setoid.Decompositions.Indecomposable][] shows that direct indecomposability is
invariant under isomorphism.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ}{𝑩 : Algebra β ρᵇ} where
  open Setoid 𝔻[ 𝑩 ] using () renaming ( sym to symᵇ )

  -- The inverse image of the congruence θ of 𝑩 under h : 𝑨 → 𝑩.
  pullbackCon : hom 𝑨 𝑩 → Con 𝑩 ℓ → Con 𝑨 ℓ
  pullbackCon (h , hhom) (_θ_ , θc) = (λ x y → (h ⟨$⟩ x) θ (h ⟨$⟩ y))
                                    , mkcon (λ e → reflexive θc (cong h e)) equiv compat
    where
    open IsEquivalence (is-equivalence θc) using () renaming ( refl to θrefl ; sym to θsym ; trans to θtrans )
    equiv : IsEquivalence (λ x y → (h ⟨$⟩ x) θ (h ⟨$⟩ y))
    equiv = record { refl = θrefl ; sym = θsym ; trans = θtrans }

    compat : 𝑨 ∣≈ (λ x y → (h ⟨$⟩ x) θ (h ⟨$⟩ y))
    compat f {u} {v} uv = θtrans  (reflexive θc (IsHom.compatible hhom))
                                  (θtrans  (is-compatible θc f uv)
                                           (reflexive θc (symᵇ (IsHom.compatible hhom))))
```


#### The canonical projection

Given an algebra `𝑨` and a congruence `θ`, the *canonical projection* is a map
from `𝑨` onto `𝑨 ╱ θ` that is constructed, and proved epimorphic, as follows.

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
