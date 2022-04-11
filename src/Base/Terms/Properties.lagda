---
layout: default
title : "Base.Terms.Properties module (The Agda Universal Algebra Library)"
date : "2021-07-03"
author: "agda-algebras development team"
---

### <a id="properties-of-terms-and-the-term-algebra">Properties of Terms and the Term Algebra</a>

This is the [Base.Terms.Properties][] module of the [Agda Universal Algebra Library][].


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Base.Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Base.Terms.Properties {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library --------------------------------------
open import Axiom.Extensionality.Propositional
                                   using () renaming (Extensionality to funext)
open import Agda.Primitive         using ( Level ; _⊔_ ; lsuc ) renaming ( Set to Type )
open import Data.Product           using ( _,_ ; Σ-syntax )
open import Function.Base          using ( _∘_ )
open import Data.Empty.Polymorphic using ( ⊥ )
open import Relation.Binary        using ( IsEquivalence ; Setoid )
open import Relation.Binary.Definitions
                                   using (Reflexive ; Symmetric ; Transitive )
open import Relation.Binary.PropositionalEquality
                                   using ( _≡_ ; refl ; module ≡-Reasoning ; cong )


-- Imports from the Agda Universal Algebra Library ----------------------------------------
open import Base.Overture.Preliminaries      using ( _⁻¹ ; 𝑖𝑑 ; ∣_∣ ; ∥_∥)
open import Base.Overture.Inverses           using ( Inv ; InvIsInverseʳ ; Image_∋_; eq )
open import Base.Overture.Surjective         using ( IsSurjective )
open import Base.Equality.Welldefined        using ( swelldef )
open import Base.Algebras.Basic              using ( Algebra ; _̂_ )
open import Base.Algebras.Products   {𝑆 = 𝑆} using ( ov )
open import Base.Homomorphisms.Basic {𝑆 = 𝑆} using ( hom )
open import Base.Terms.Basic         {𝑆 = 𝑆}

private variable α β χ : Level

\end{code}


#### <a id="the-universal-property">The universal property</a>

The term algebra `𝑻 X` is *absolutely free* (or *universal*, or *initial*) for algebras in the signature `𝑆`. That is, for every 𝑆-algebra `𝑨`, the following hold.

1. Every function from `𝑋` to `∣ 𝑨 ∣` lifts to a homomorphism from `𝑻 X` to `𝑨`.
2. The homomorphism that exists by item 1 is unique.

We now prove this in [Agda][], starting with the fact that every map from `X` to `∣ 𝑨 ∣` lifts to a map from `∣ 𝑻 X ∣` to `∣ 𝑨 ∣` in a natural way, by induction on the structure of the given term.

\begin{code}

private variable X : Type χ

free-lift : (𝑨 : Algebra α 𝑆)(h : X → ∣ 𝑨 ∣) → ∣ 𝑻 X ∣ → ∣ 𝑨 ∣
free-lift _ h (ℊ x) = h x
free-lift 𝑨 h (node f 𝑡) = (f ̂ 𝑨) (λ i → free-lift 𝑨 h (𝑡 i))

\end{code}

Naturally, at the base step of the induction, when the term has the form `generator`
x, the free lift of `h` agrees with `h`.  For the inductive step, when the
given term has the form `node f 𝑡`, the free lift is defined as
follows: Assuming (the induction hypothesis) that we know the image of each
subterm `𝑡 i` under the free lift of `h`, define the free lift at the
full term by applying `f ̂ 𝑨` to the images of the subterms.

The free lift so defined is a homomorphism by construction. Indeed, here is the trivial proof.

\begin{code}

lift-hom : (𝑨 : Algebra α 𝑆) → (X → ∣ 𝑨 ∣) → hom (𝑻 X) 𝑨
lift-hom 𝑨 h = free-lift 𝑨 h , λ f a → cong (f ̂ 𝑨) refl

\end{code}

Finally, we prove that the homomorphism is unique.  This requires `funext 𝓥 α` (i.e., *function extensionality* at universe levels `𝓥` and `α`) which we postulate by making it part of the premise in the following function type definition.

\begin{code}

open ≡-Reasoning

free-unique : swelldef 𝓥 α → (𝑨 : Algebra α 𝑆)(g h : hom (𝑻 X) 𝑨)
 →            (∀ x → ∣ g ∣ (ℊ x) ≡ ∣ h ∣ (ℊ x))
              ----------------------------------------
 →            ∀ (t : Term X) →  ∣ g ∣ t ≡ ∣ h ∣ t

free-unique _ _ _ _ p (ℊ x) = p x

free-unique wd 𝑨 g h p (node 𝑓 𝑡) =

 ∣ g ∣ (node 𝑓 𝑡)    ≡⟨ ∥ g ∥ 𝑓 𝑡 ⟩
 (𝑓 ̂ 𝑨)(∣ g ∣ ∘ 𝑡)  ≡⟨ wd (𝑓 ̂ 𝑨)(∣ g ∣ ∘ 𝑡)(∣ h ∣ ∘ 𝑡)(λ i → free-unique wd 𝑨 g h p (𝑡 i)) ⟩
 (𝑓 ̂ 𝑨)(∣ h ∣ ∘ 𝑡)  ≡⟨ (∥ h ∥ 𝑓 𝑡)⁻¹ ⟩
 ∣ h ∣ (node 𝑓 𝑡)    ∎

\end{code}

Let's account for what we have proved thus far about the term algebra.  If we postulate a type `X : Type χ` (representing an arbitrary collection of variable symbols) such that for each `𝑆`-algebra `𝑨` there is a map from `X` to the domain of `𝑨`, then it follows that for every `𝑆`-algebra `𝑨` there is a homomorphism from `𝑻 X` to `∣ 𝑨 ∣` that "agrees with the original map on `X`," by which we mean that for all `x : X` the lift evaluated at `ℊ x` is equal to the original function evaluated at `x`.

If we further assume that each of the mappings from `X` to `∣ 𝑨 ∣` is *surjective*, then the homomorphisms constructed with `free-lift` and `lift-hom` are *epimorphisms*, as we now prove.

\begin{code}

lift-of-epi-is-epi : (𝑨 : Algebra α 𝑆){h₀ : X → ∣ 𝑨 ∣}
 →                   IsSurjective h₀ → IsSurjective ∣ lift-hom 𝑨 h₀ ∣

lift-of-epi-is-epi 𝑨 {h₀} hE y = Goal
 where
 h₀⁻¹y = Inv h₀ (hE y)

 η : y ≡ ∣ lift-hom 𝑨 h₀ ∣ (ℊ h₀⁻¹y)
 η = (InvIsInverseʳ (hE y))⁻¹

 Goal : Image ∣ lift-hom 𝑨 h₀ ∣ ∋ y
 Goal = eq (ℊ h₀⁻¹y) η

\end{code}

The `lift-hom` and `lift-of-epi-is-epi` types will be called to action when such epimorphisms are needed later (e.g., in the [Base.Varieties][] module).

------------------------------

<span style="float:left;">[← Base.Terms.Basic](Base.Terms.Basic.html)</span>
<span style="float:right;">[Base.Terms.Operations →](Base.Terms.Operations.html)</span>

{% include UALib.Links.md %}
