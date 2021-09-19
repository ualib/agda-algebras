---
layout: default
title : "Overture.Surjective module"
date : "2021-01-12"
author: "the agda-algebras development team"
---

### <a id="surjective-functions">Surjective functions</a>

This is the [Overture.Surjective][] module of the [agda-algebras][] library.
\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}
module Overture.Surjective where

-- Imports from Agda and the Agda Standard Library -------------------------------------------
open import Agda.Primitive                        using ( _⊔_ ; Level ) renaming ( Set to Type )
open import Data.Product                          using ( _,_ ; Σ )
open import Function.Base                         using ( _∘_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; module ≡-Reasoning ; cong-app )

-- Imports from agda-algebras ----------------------------------------------------------------
open import Overture.Preliminaries using ( _≈_ ; _⁻¹ ; _∙_ )
open import Overture.Inverses      using ( Image_∋_ ; Inv ; InvIsInverseʳ )

private variable α β γ : Level

\end{code}

#### <a id="epics">Surjective functions</a>

A *surjective function* from `A` to `B` is a function `f : A → B` such that for all `b : B` there exists `a : A` such that `f a ≡ b`.  In other words, the range and codomain of `f` agree.  The following types manifest this notion.

\begin{code}

module _ {A : Type α}{B : Type β} where
 IsSurjective : (A → B) →  Type (α ⊔ β)
 IsSurjective f = ∀ y → Image f ∋ y

 Surjective : Type (α ⊔ β)
 Surjective = Σ (A → B) IsSurjective

\end{code}
With the next definition, we can represent a *right-inverse* of a surjective function.
\begin{code}

 SurjInv : (f : A → B) → IsSurjective f → B → A
 SurjInv f fE b = Inv f (fE b)

\end{code}
Thus, a right-inverse of `f` is obtained by applying `SurjInv` to `f` and a proof of `IsSurjective f`.  Next we prove that this does indeed give the right-inverse.
\begin{code}

module _ {A : Type α}{B : Type β} where

 SurjInvIsInverseʳ : (f : A → B)(fE : IsSurjective f) → ∀ b → f ((SurjInv f fE) b) ≡ b
 SurjInvIsInverseʳ f fE b = InvIsInverseʳ (fE b)

 open ≡-Reasoning
 open Image_∋_

 -- composition law for epics
 epic-factor : {C : Type γ}(f : A → B)(g : A → C)(h : C → B)
  →            f ≈ h ∘ g → IsSurjective f → IsSurjective h

 epic-factor f g h compId fe y = Goal
  where
   finv : B → A
   finv = SurjInv f fe

   ζ : y ≡ f (finv y)
   ζ = (SurjInvIsInverseʳ f fe y)⁻¹

   η : y ≡ (h ∘ g) (finv y)
   η = ζ ∙ compId (finv y)

   Goal : Image h ∋ y
   Goal = eq (g (finv y)) η

 epic-factor-intensional : {C : Type γ}(f : A → B)(g : A → C)(h : C → B)
  →                        f ≡ h ∘ g → IsSurjective f → IsSurjective h

 epic-factor-intensional f g h compId fe y = Goal
  where
   finv : B → A
   finv = SurjInv f fe

   ζ : f (finv y) ≡ y
   ζ = SurjInvIsInverseʳ f fe y

   η : (h ∘ g) (finv y) ≡ y
   η = (cong-app (compId ⁻¹)(finv y)) ∙ ζ

   Goal : Image h ∋ y
   Goal = eq (g (finv y)) (η ⁻¹)

\end{code}

--------------------------------------

<span style="float:left;">[← Overture.Injective](Overture.Injective.html)</span>
<span style="float:right;">[Overture.Transformers →](Overture.Transformers.html)</span>

{% include UALib.Links.md %}


