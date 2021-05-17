---
layout: default
title : Overture.Inverses module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="inverses">Inverses</a>

This is the [Overture.Inverses][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

-- Imports from the Agda (Builtin) and the Agda Standard Library
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (_⊔_; lzero; lsuc; Level; Setω)
open import Data.Product using (_,_; Σ; Σ-syntax; _×_)
open import Function.Base  using (_∘_; id)
open import Relation.Binary.PropositionalEquality.Core using (subst; cong-app)

-- Imports from the Agda Universal Algebra Library
open import Overture.Preliminaries using (Type; 𝓤; 𝓥; 𝓦; 𝓩; _⁻¹; Π; -Π; -Σ; _∙_; 𝑖𝑑; _∼_)

module Overture.Inverses where

\end{code}

We begin by defining an data type that represents the semantic concept of *inverse image* of a function.

\begin{code}

module _ {A : Type 𝓤 }{B : Type 𝓦 } where

 data Image_∋_ (f : A → B) : B → Type (𝓤 ⊔ 𝓦)
  where
  eq : {b : B} → (a : A) → b ≡ f a → Image f ∋ b

\end{code}

An inhabitant of `Image f ∋ b` is a dependent pair `(a , p)`, where `a : A` and `p : b ≡ f a` is a proof that `f` maps `a` to `b`.  Since the proof that `b` belongs to the image of `f` is always accompanied by a witness `a : A`, we can actually *compute* a (pseudo)inverse of `f`. For convenience, we define this inverse function, which we call `Inv`, and which takes an arbitrary `b : B` and a (*witness*, *proof*)-pair, `(a , p) : Image f ∋ b`, and returns the witness `a`.

\begin{code}

 Inv : (f : A → B){b : B} → Image f ∋ b  →  A
 Inv f (eq a _) = a

\end{code}

We can prove that `Inv f` is the *right-inverse* of `f`, as follows.

\begin{code}

 InvIsInv : (f : A → B){b : B}(q : Image f ∋ b) → f(Inv f q) ≡ b
 InvIsInv f (eq _ p) = p ⁻¹

\end{code}


#### <a id="injective-functions">Injective functions</a>

We say that a function `f : A → B` is *injective* (or *monic*) if it does not map two distinct elements of the domain to the same point in the codomain. The following types manifest this property.

\begin{code}

module _ {A : Type 𝓤}{B : Type 𝓦} where

 IsInjective : (A → B) → Type (𝓤 ⊔ 𝓦)
 IsInjective f = ∀ {x y} → f x ≡ f y → x ≡ y

 Injective : Type (𝓤 ⊔ 𝓦)
 Injective = Σ[ f ꞉ (A → B) ] IsInjective f

\end{code}


Before moving on to discuss surjective functions, let us prove (the obvious facts) that the identity map is injective and that the composition of injectives is injective.


\begin{code}

id-is-injective : {A : Type 𝓤} → IsInjective{A = A}{B = A} (λ x → x)
id-is-injective = λ z → z

∘-injective : {A : Type 𝓤}{B : Type 𝓦}{C : Type 𝓩}{f : A → B}{g : B → C}
 →            IsInjective f → IsInjective g → IsInjective (g ∘ f)
∘-injective finj ginj = λ z → finj (ginj z)

\end{code}


#### <a id="epics">Surjective functions</a>

A *surjective function* from `A` to `B` is a function `f : A → B` such that for all `b : B` there exists `a : A` such that `f a ≡ b`.  In other words, the range and codomain of `f` agree.  The following types manifest this notion.

\begin{code}

module _ {A : Type 𝓤}{B : Type 𝓦} where
 IsSurjective : (A → B) →  Type (𝓤 ⊔ 𝓦)
 IsSurjective f = ∀ y → Image f ∋ y

 Surjective : Type (𝓤 ⊔ 𝓦)
 Surjective = Σ[ f ꞉ (A → B) ] IsSurjective f

\end{code}

With the next definition, we can represent a *right-inverse* of a surjective function.

\begin{code}

 SurjInv : (f : A → B) → IsSurjective f → B → A
 SurjInv f fE b = Inv f (fE b)

\end{code}

Thus, a right-inverse of `f` is obtained by applying `SurjInv` to `f` and a proof of `IsSurjective f`.  Later, we will prove that this does indeed give the right-inverse, but we postpone the proof since it requires function extensionality, a concept we take up in the [Relations.Extensionality][] module.


-------------------------------------

<p></p>

[← Overture.Preliminaries](Overture.Preliminaries.html)
<span style="float:right;">[Relations →](Relations.html)</span>


{% include UALib.Links.md %}
