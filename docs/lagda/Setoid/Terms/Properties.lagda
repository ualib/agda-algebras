---
layout: default
title : "Setoid.Terms.Properties module (The Agda Universal Algebra Library)"
date : "2021-09-18"
author: "agda-algebras development team"
---

#### <a id="basic-properties">Basic properties of terms on setoids</a>

This is the [Setoid.Terms.Properties][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Terms.Properties {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ---------------------
open import Agda.Primitive   using () renaming ( Set to Type )
open import Data.Product     using ( _,_ )
open import Function.Bundles using () renaming ( Func to _⟶_ )
open import Function.Base    using ( _∘_ )
open import Level            using ( Level )
open import Relation.Binary  using ( Setoid )
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture          using ( ∣_∣ ; ∥_∥ )
open import Setoid.Functions  using ( Img_∋_ ; eq ; isSurj ; IsSurjective )
                              using ( isSurj→IsSurjective )

open import Base.Terms            {𝑆 = 𝑆} using ( Term )
open import Setoid.Algebras       {𝑆 = 𝑆} using ( Algebra ; 𝕌[_] ; _̂_ )
open import Setoid.Homomorphisms  {𝑆 = 𝑆} using ( hom ; compatible-map ; IsHom )
open import Setoid.Terms.Basic    {𝑆 = 𝑆}  using ( 𝑻 ; _≐_  ; ≐-isRefl )

open Term
open _⟶_ using ( cong ) renaming ( to to _⟨$⟩_ )

private variable
 α ρᵃ β ρᵇ ρ χ : Level
 X : Type χ

\end{code}

The term algebra `𝑻 X` is *absolutely free* (or *universal*, or *initial*) for
algebras in the signature `𝑆`. That is, for every 𝑆-algebra `𝑨`, the following hold.

1. Every function from `𝑋` to `∣ 𝑨 ∣` lifts to a homomorphism from `𝑻 X` to `𝑨`.
2. The homomorphism that exists by item 1 is unique.

We now prove this in [Agda][], starting with the fact that every map from `X` to
`∣ 𝑨 ∣` lifts to a map from `∣ 𝑻 X ∣` to `∣ 𝑨 ∣` in a natural way, by induction
on the structure of the given term.

\begin{code}

module _ {𝑨 : Algebra α ρ}(h : X → 𝕌[ 𝑨 ]) where
 open Algebra 𝑨      using ( Interp )                   renaming ( Domain to A )
 open Setoid A       using ( _≈_ ; reflexive ; trans )  renaming ( Carrier to ∣A∣ )
 open Algebra (𝑻 X)  using ()                           renaming ( Domain to TX )
 open Setoid TX      using ()                           renaming ( Carrier to ∣TX∣ )

 free-lift : 𝕌[ 𝑻 X ] → 𝕌[ 𝑨 ]
 free-lift (ℊ x) = h x
 free-lift (node f t) = (f ̂ 𝑨) (λ i → free-lift (t i))

 free-lift-of-surj-isSurj :  isSurj{𝑨 = ≡.setoid X}{𝑩 = A} h
  →                          isSurj{𝑨 = TX}{𝑩 = A} free-lift

 free-lift-of-surj-isSurj hE {y} = mp p
  where
  p : Img h ∋ y
  p = hE
  mp : Img h ∋ y → Img free-lift ∋ y
  mp (eq a x) = eq (ℊ a) x

 free-lift-func : TX ⟶ A
 free-lift-func ⟨$⟩ x = free-lift x
 cong free-lift-func = flcong
  where
  flcong : ∀ {s t} → s ≐ t →  free-lift s ≈ free-lift t
  flcong (_≐_.rfl x) = reflexive (≡.cong h x)
  flcong (_≐_.gnl x) = cong Interp (≡.refl , (λ i → flcong (x i)))

\end{code}

Naturally, at the base step of the induction, when the term has the form `generator`
x, the free lift of `h` agrees with `h`.  For the inductive step, when the given term
has the form `node f t`, the free lift is defined as follows: Assuming (the induction
hypothesis) that we know the image of each subterm `t i` under the free lift of `h`,
define the free lift at the full term by applying `f ̂ 𝑨` to the images of the subterms.

The free lift so defined is a homomorphism by construction. Indeed, here is the trivial proof.

\begin{code}

 lift-hom : hom (𝑻 X) 𝑨
 lift-hom = free-lift-func , hhom
  where
  hfunc : TX ⟶ A
  hfunc = free-lift-func

  hcomp : compatible-map (𝑻 X) 𝑨 free-lift-func
  hcomp {f}{a} = cong Interp (≡.refl , (λ i → (cong free-lift-func){a i} ≐-isRefl))

  hhom : IsHom (𝑻 X) 𝑨 hfunc
  hhom = record { compatible = λ{f}{a} → hcomp{f}{a} }

\end{code}

If we further assume that each of the mappings from `X` to `∣ 𝑨 ∣` is *surjective*, then the homomorphisms constructed with `free-lift` and `lift-hom` are *epimorphisms*, as we now prove.

\begin{code}

 lift-of-epi-is-epi : isSurj{𝑨 = ≡.setoid X}{𝑩 = A} h → IsSurjective free-lift-func
 lift-of-epi-is-epi hE = isSurj→IsSurjective free-lift-func (free-lift-of-surj-isSurj hE)

\end{code}

Finally, we prove that the homomorphism is unique.  Recall, when we proved this in the module
[Basic.Terms.Properties][], we needed function extensionality. Here, by using setoid equality,
we can omit the `swelldef` hypothesis we needed previously to prove `free-unique`.

\begin{code}

module _ {𝑨 : Algebra α ρ}{gh hh : hom (𝑻 X) 𝑨} where
 open Algebra 𝑨      using ( Interp )  renaming ( Domain to A )
 open Setoid A       using ( _≈_ ; trans ; sym )
 open Algebra (𝑻 X)  using ()          renaming ( Domain to TX )
 open _≐_
 open IsHom

 private
  g = _⟨$⟩_ ∣ gh ∣
  h = _⟨$⟩_ ∣ hh ∣

 free-unique : (∀ x → g (ℊ x) ≈ h (ℊ x)) → ∀ (t : Term X) →  g t ≈ h t
 free-unique p (ℊ x) = p x
 free-unique p (node f t) = trans (trans geq lem3) (sym heq)
  where
  lem2 : ∀ i → (g (t i)) ≈ (h (t i))
  lem2 i = free-unique p (t i)

  lem3 : (f ̂ 𝑨)(λ i → (g (t i))) ≈ (f ̂ 𝑨)(λ i → (h (t i)))
  lem3 = cong Interp (_≡_.refl , lem2)

  geq : (g (node f t)) ≈ (f ̂ 𝑨)(λ i → (g (t i)))
  geq = compatible ∥ gh ∥

  heq : h (node f t) ≈ (f ̂ 𝑨)(λ i → h (t i))
  heq = compatible ∥ hh ∥
\end{code}

------------------------------

<span style="float:left;">[← Setoid.Terms.Basic](Setoid.Terms.Basic.html)</span>
<span style="float:right;">[Setoid.Terms.Operations →](Setoid.Terms.Operations.html)</span>

{% include UALib.Links.md %}


