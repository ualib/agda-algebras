{-
layout: default
title : Overture.Inverses module
date : 2021-01-12
author: the agda-algebras development team
-}

-- Inverses
-- ========
--
-- This is the [Overture.Inverses][] module of the [agda-algebras][] library.

{-# OPTIONS --without-K --exact-split --safe #-}

module Overture.Inverses where

open import stdlib-imports
open import Overture.Preliminaries using (_⁻¹; _∙_; 𝑖𝑑; _∼_)

private
  variable
    𝓤 𝓥 𝓦 𝓩 : Level

-- We begin by defining an data type that represents the semantic concept of *inverse image* of a function.

module _ {A : Type 𝓤 }{B : Type 𝓦 } where

 data Image_∋_ (f : A → B) : B → Type (𝓤 ⊔ 𝓦) where
  eq : {b : B} → (a : A) → b ≡ f a → Image f ∋ b

-- An inhabitant of `Image f ∋ b` is a dependent pair `(a , p)`, where `a : A` and `p : b ≡ f a` is a proof
-- that `f` maps `a` to `b`.  Since the proof that `b` belongs to the image of `f` is always accompanied by
-- a witness `a : A`, we can actually *compute* a (pseudo)inverse of `f`. For convenience, we define this
-- inverse function, which we call `Inv`, and which takes an arbitrary `b : B` and a
-- (*witness*, *proof*)-pair, `(a , p) : Image f ∋ b`, and returns the witness `a`.

 Inv : (f : A → B){b : B} → Image f ∋ b  →  A
 Inv f (eq a _) = a

-- We can prove that `Inv f` is the *right-inverse* of `f`, as follows.

 InvIsInv : (f : A → B){b : B}(q : Image f ∋ b) → f(Inv f q) ≡ b
 InvIsInv f (eq _ p) = p ⁻¹


-- Injective functions
-- --------------------
-- We say that a function `f : A → B` is *injective* (or *monic*) if it does not map two distinct elements of
-- the domain to the same point in the codomain. The following type manifests this property.

module _ {A : Type 𝓤}{B : Type 𝓦} where

 IsInjective : (A → B) → Type (𝓤 ⊔ 𝓦)
 IsInjective f = Injective _≡_ _≡_ f

-- Before moving on to discuss surjective functions, let us prove (the obvious facts) that the identity map is
-- injective and that the composition of injectives is injective.

id-is-injective : {A : Type 𝓤} → A ↣ A
id-is-injective {A = A} = id-↣ A

∘-injective : {A : Type 𝓤}{B : Type 𝓦}{C : Type 𝓩}{f : A → B}{g : B → C}
 →            IsInjective f → IsInjective g → IsInjective (g ∘ f)
∘-injective finj ginj = λ z → finj (ginj z)


-- Surjective functions
-- --------------------
-- A *surjective function* from `A` to `B` is a function `f : A → B` such that for all `b : B` there exists
-- `a : A` such that `f a ≡ b`.  In other words, the range and codomain of `f` agree.  The following types
-- manifest this notion.

module _ {A : Type 𝓤}{B : Type 𝓦} where
 IsSurjective : (A → B) →  Type (𝓤 ⊔ 𝓦)
 IsSurjective f = ∀ y → Image f ∋ y

 Surjective : Type (𝓤 ⊔ 𝓦)
 Surjective = Σ (A → B) IsSurjective

-- With the next definition, we can represent a *right-inverse* of a surjective function.

 SurjInv : (f : A → B) → IsSurjective f → B → A
 SurjInv f fE b = Inv f (fE b)

-- Thus, a right-inverse of `f` is obtained by applying `SurjInv` to `f` and a proof of `IsSurjective f`.
-- Later, we will prove that this does indeed give the right-inverse, but we postpone the proof since it
-- requires function extensionality, a concept we take up in the [Relations.Extensionality][] module.

