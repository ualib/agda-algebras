---
layout: default
title : Overture.Inverses module
date : 2021-01-12
author: [agda-algebras development team][]
---

### <a id="inverses">Inverses</a>

This is the [Overture.Inverses][] module of the [agda-algebras][] library.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


module Overture.Inverses where

-- Imports from Agda and the Agda Standard Library ---------------------------------------------
open import Agda.Primitive              using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type )
open import Data.Product                using ( _,_ ; _×_ ; Σ )
open import Function.Base               using ( _∘_ )
open import Function.Definitions        using ( Injective )
open import Function.Bundles            using ( _↣_ ; mk↣ )
open import Function.Construct.Identity using ( id-↣ )
open import Relation.Binary.PropositionalEquality
                                        using ( _≡_ ; refl ; module ≡-Reasoning ; cong-app )

-- Imports from agda-algebras
open import Overture.Preliminaries using ( _⁻¹ ; _≈_ ; _∙_ )

\end{code}

We begin by defining an data type that represents the semantic concept of *inverse image* of a function.

\begin{code}

private variable α β γ : Level

module _ {A : Type α }{B : Type β } where

 data Image_∋_ (f : A → B) : B → Type (α ⊔ β) where
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

We say that a function `f : A → B` is *injective* (or *monic*) if it does not map two distinct elements of the domain to the same point in the codomain. The following type manifests this property.

\begin{code}

module _ {A : Type α}{B : Type β} where

 IsInjective : (A → B) → Type (α ⊔ β)
 IsInjective f = Injective _≡_ _≡_ f

\end{code}

Before moving on to discuss surjective functions, let us prove (the obvious facts) that the identity map is injective and that the composition of injectives is injective.

\begin{code}

id-is-injective : {A : Type α} → A ↣ A
id-is-injective {A = A} = id-↣ A

∘-injective : {A : Type α}{B : Type β}{C : Type γ}{f : A → B}{g : B → C}
 →            IsInjective f → IsInjective g → IsInjective (g ∘ f)
∘-injective finj ginj = λ z → finj (ginj z)

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

 SurjInvIsRightInv : (f : A → B)(fE : IsSurjective f) → ∀ b → f ((SurjInv f fE) b) ≡ b
 SurjInvIsRightInv f fE b = InvIsInv f (fE b)

 open ≡-Reasoning

 -- composition law for epics
 epic-factor : {C : Type γ}(f : A → B)(g : A → C)(h : C → B)
  →            f ≈ h ∘ g → IsSurjective f → IsSurjective h

 epic-factor f g h compId fe y = Goal
  where
   finv : B → A
   finv = SurjInv f fe

   ζ : y ≡ f (finv y)
   ζ = (SurjInvIsRightInv f fe y)⁻¹

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
   ζ = SurjInvIsRightInv f fe y

   η : (h ∘ g) (finv y) ≡ y
   η = (cong-app (compId ⁻¹)(finv y)) ∙ ζ

   Goal : Image h ∋ y
   Goal = eq (g (finv y)) (η ⁻¹)

\end{code}


--------------------------------------

[← Overture.Preliminaries](Overture.Preliminaries.html)
<span style="float:right;">[Overture.Transformers →](Overture.Transformers.html)</span>


{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team


