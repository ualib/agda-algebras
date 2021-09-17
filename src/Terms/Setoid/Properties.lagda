---
layout: default
title : "Terms.Setoid.Properties module (The Agda Universal Algebra Library)"
date : "2021-08-24"
author: "agda-algebras development team"
---

#### <a id="basic-properties">Basic properties</a>

This is the [Terms.Setoid.Properties][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Terms.Setoid.Properties {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ---------------------
open import Axiom.Extensionality.Propositional
                                   using () renaming (Extensionality to funext)
open import Agda.Primitive         using ( Level ; _⊔_ ; lsuc ) renaming ( Set to Type )
open import Data.Product           using ( _,_ ; Σ-syntax ) renaming (proj₂ to snd)
open import Function.Base          using ( _∘_ )
open import Function.Equality using ( Π ; _⟶_ )
open import Function.Bundles       using ( Func )
open import Data.Empty.Polymorphic using ( ⊥ )
open import Relation.Binary        using ( IsEquivalence ; Setoid )
open import Relation.Binary.Definitions using (Reflexive ; Symmetric ; Transitive )
open import Relation.Binary.PropositionalEquality as PE
                                   using ( _≡_ ; refl ; module ≡-Reasoning )

-- Imports from the Agda Universal Algebra Library ------------------------------------------------
open import Overture.Preliminaries using ( _⁻¹ ; 𝑖𝑑 ; ∣_∣ ; ∥_∥ ; transport )
open import Overture.Setoid.Inverses      using ( Inv ; InvIsInv ; Image_∋_ ; eq )
open import Overture.Setoid.Surjective    using ( IsSurjective )

open import Algebras.Setoid.Basic      {𝑆 = 𝑆} using ( SetoidAlgebra ; _̂_ ; ov ; 𝕌[_] )
open import Homomorphisms.Setoid.Basic {𝑆 = 𝑆} using ( hom ; IsHom )
open import Terms.Setoid.Basic         {𝑆 = 𝑆} using ( Term ; 𝑻 ; _≐_ )
open Term

private variable α ρ χ : Level

\end{code}

The term algebra `𝑻 X` is *absolutely free* (or *universal*, or *initial*) for algebras in the signature `𝑆`. That is, for every 𝑆-algebra `𝑨`, the following hold.

1. Every function from `𝑋` to `∣ 𝑨 ∣` lifts to a homomorphism from `𝑻 X` to `𝑨`.
2. The homomorphism that exists by item 1 is unique.

We now prove this in [Agda][], starting with the fact that every map from `X` to `∣ 𝑨 ∣` lifts to a map from `∣ 𝑻 X ∣` to `∣ 𝑨 ∣` in a natural way, by induction on the structure of the given term.

\begin{code}

private variable X : Type χ

open SetoidAlgebra
open Setoid
open Π

-- NEXT: use _≐_ from Terms/Setoid/Basic

free-lift : (𝑨 : SetoidAlgebra α ρ)(h : X → 𝕌[ 𝑨 ]) → Domain (𝑻 X) ⟶ Domain 𝑨
free-lift {X = X} 𝑨 h = record { _⟨$⟩_ = ap ; cong = c }
 where
 ap : 𝕌[ 𝑻 X ] → 𝕌[ 𝑨 ]
 c : ∀ {t₀ t₁} → (_≈_ (Domain (𝑻 X))) t₀ t₁ → (_≈_ (Domain 𝑨)) (ap t₀) (ap t₁)
 ap (ℊ x) = h x
 ap (node f t) = (f ̂ 𝑨) (λ i → free-lift 𝑨 h ⟨$⟩ (t i))
 c {t₀}{t₁} = {!!}
-- ⟨$⟩ ℊ x = h x
-- free-lift 𝑨 h ⟨$⟩ node f t = {!!} -- (f ̂ 𝑨) (λ i → (free-lift 𝑨 h) ⟨$⟩ (t i))
-- cong (free-lift 𝑨 h) = λ x → {!!}

-- free-lift : (𝑨 : SetoidAlgebra α ρ)(h : X → 𝕌[ 𝑨 ]) → 𝕌[ 𝑻 X ] → 𝕌[ 𝑨 ]
-- free-lift _ h (ℊ x) = h x
-- free-lift 𝑨 h (node f t) = (f ̂ 𝑨) (λ i → free-lift 𝑨 h (t i))

\end{code}

Naturally, at the base step of the induction, when the term has the form `generator`
x, the free lift of `h` agrees with `h`.  For the inductive step, when the
given term has the form `node f t`, the free lift is defined as
follows: Assuming (the induction hypothesis) that we know the image of each
subterm `t i` under the free lift of `h`, define the free lift at the
full term by applying `f ̂ 𝑨` to the images of the subterms.

The free lift so defined is a homomorphism by construction. Indeed, here is the trivial proof.

\begin{code}

lift-hom : (𝑨 : SetoidAlgebra α ρ) → (X → 𝕌[ 𝑨 ]) → hom (𝑻 X) 𝑨
lift-hom 𝑨 h = free-lift 𝑨 h , record { compatible = {!!} ; preserves≈ = {!!} } -- λ f a → cong (f ̂ 𝑨) refl

\end{code}

Finally, we prove that the homomorphism is unique.  Recall, when we proved this in the module [Terms.Properties][], we needed function extensionality. Here, by using setoid equality, we can omit the `swelldef` hypothesis used to prove `free-unique` in the [Terms.Properties][] module.

\begin{code}

module _ {𝑨 : SetoidAlgebra α ρ} where
 open SetoidAlgebra 𝑨
 open Setoid
 open IsHom
 open Π
 private
  A = Domain 𝑨
  _≈A≈_ = _≈_ A

 free-unique : {g h : hom (𝑻 X) 𝑨}
  →            (∀ x → (∣ g ∣ ⟨$⟩ (ℊ x)) ≈A≈ (∣ h ∣ ⟨$⟩ (ℊ x)))
               --------------------------------------
  →            ∀ (t : Term X) →  (∣ g ∣ ⟨$⟩ t) ≈A≈ (∣ h ∣ ⟨$⟩ t)

 free-unique p (ℊ x) = p x

 free-unique {g = g} {h} p (node f t) = trans A (trans A geq lem3) (sym A heq)
  where
  lem2 : ∀ i → (∣ g ∣ ⟨$⟩ (t i)) ≈A≈ (∣ h ∣ ⟨$⟩ (t i))
  lem2 i = free-unique{g = g}{h} p (t i)

  lem3 : (f ̂ 𝑨)(λ i → (∣ g ∣ ⟨$⟩ (t i))) ≈A≈ (f ̂ 𝑨)(λ i → (∣ h ∣ ⟨$⟩ (t i)))
  lem3 = Func.cong (Interp 𝑨) (_≡_.refl , lem2)

  geq : (∣ g ∣ ⟨$⟩ (node f t)) ≈A≈ (f ̂ 𝑨)(λ i → (∣ g ∣ ⟨$⟩ (t i)))
  geq = (compatible ∥ g ∥) f t

  heq : (∣ h ∣ ⟨$⟩ (node f t)) ≈A≈ (f ̂ 𝑨)(λ i → (∣ h ∣ ⟨$⟩ (t i)))
  heq = compatible ∥ h ∥ f t

\end{code}

Let's account for what we have proved thus far about the term algebra.  If we postulate a type `X : Type χ` (representing an arbitrary collection of variable symbols) such that for each `𝑆`-algebra `𝑨` there is a map from `X` to the domain of `𝑨`, then it follows that for every `𝑆`-algebra `𝑨` there is a homomorphism from `𝑻 X` to `∣ 𝑨 ∣` that "agrees with the original map on `X`," by which we mean that for all `x : X` the lift evaluated at `ℊ x` is equal to the original function evaluated at `x`.

If we further assume that each of the mappings from `X` to `∣ 𝑨 ∣` is *surjective*, then the homomorphisms constructed with `free-lift` and `lift-hom` are *epimorphisms*, as we now prove.

\begin{code}

 lift-of-epi-is-epi : (h₀ : X → 𝕌[ 𝑨 ])
  →                   IsSurjective (free-lift 𝑨 h₀) → IsSurjective ∣ lift-hom 𝑨 h₀ ∣

 lift-of-epi-is-epi h₀ hE y = Goal
  where
  h₀⁻¹y = Inv (free-lift 𝑨 h₀) (hE y)

  η : y ≈A≈ (∣ lift-hom 𝑨 h₀ ∣ ⟨$⟩ h₀⁻¹y)
  η = sym A (InvIsInv (free-lift 𝑨 h₀) (hE y))

  Goal : Image ∣ lift-hom 𝑨 h₀ ∣ ∋ y
  Goal = eq h₀⁻¹y η

\end{code}

The `lift-hom` and `lift-of-epi-is-epi` types will be called to action when such epimorphisms are needed later (e.g., in the [Varieties][] module).

------------------------------

<span style="float:left;">[← Terms.Setoid.Basic](Terms.Setoid.Basic.html)</span>
<span style="float:right;">[Subalgebras →](Subalgebras.html)</span>

{% include UALib.Links.md %}
