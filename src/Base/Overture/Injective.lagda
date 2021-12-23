---
layout: default
title : "Base.Overture.Injective module"
date : "2021-09-10"
author: "the agda-algebras development team"
---

### <a id="injective-functions">Injective functions</a>

This is the [Base.Overture.Injective][] module of the [agda-algebras][] library.

We say that a function `f : A → B` is *injective* (or *monic*) if it does not map two distinct elements of the domain to the same point in the codomain. The following type manifests this property.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Base.Overture.Injective where

-- Imports from Agda and the Agda Standard Library ---------------------------------------------
open import Agda.Primitive   using ( _⊔_ ; Level ) renaming ( Set to Type )
open import Function.Bundles                      using ( _↣_ )
open import Function.Construct.Identity           using ( id-↣ )
open import Function.Base                         using ( _∘_ )
open import Function.Definitions as FD            using ( Injective )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )
open import Relation.Binary  using ( Rel )


private variable α β γ ℓ₁ ℓ₂ ℓ₃ : Level


id-is-injective : {A : Type α} → A ↣ A
id-is-injective {A = A} = id-↣ A

module _ {A : Type α}{B : Type β} where

 IsInjective : (A → B) → Type (α ⊔ β)
 IsInjective f = Injective _≡_ _≡_ f

\end{code}

Next, we prove that the composition of injective functions is injective.

\begin{code}

∘-injective : {A : Type α}{B : Type β}{C : Type γ}{f : A → B}{g : B → C}
  →           IsInjective f → IsInjective g → IsInjective (g ∘ f)
∘-injective fi gi = λ x → fi (gi x)

\end{code}

--------------------------------------

<span style="float:left;">[← Base.Overture.FuncInverses](Base.Overture.FuncInverses.html)</span>
<span style="float:right;">[Base.Overture.Surjective →](Base.Overture.Surjective.html)</span>

{% include UALib.Links.md %}


