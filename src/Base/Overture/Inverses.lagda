---
layout: default
title : "Base.Overture.Inverses module"
date : "2021-01-12"
author: "the agda-algebras development team"
---

### <a id="inverses">Inverses</a>

This is the [Base.Overture.Inverses][] module of the [agda-algebras][] library.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}
module Base.Overture.Inverses where

-- Imports from Agda and the Agda Standard Library ---------------------------------------------
open import Agda.Primitive                        using ( _⊔_ ; Level ) renaming ( Set to Type )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; sym ; refl )
open import Relation.Unary    using ( Pred ; _∈_ )
open import Data.Product      using ( _,_ ; Σ-syntax )

-- Imports from agda-algebras ----------------------------------------------------------------
open import Base.Overture.Preliminaries using ( ∃-syntax ; ∣_∣ )

private variable α β : Level

\end{code}

We begin by defining an data type that represents the semantic concept of *inverse image* of a function.

\begin{code}

module _ {A : Type α }{B : Type β } where

 data Image_∋_ (f : A → B) : B → Type (α ⊔ β) where
  eq : {b : B} → (a : A) → b ≡ f a → Image f ∋ b

 open Image_∋_

 Range : (A → B) → Pred B (α ⊔ β)
 Range f b = ∃[ a ∈ A ] (f a) ≡ b

 range : (A → B) → Type (α ⊔ β)
 range f = Σ[ b ∈ B ] ∃[ a ∈ A ](f a) ≡ b

 Image⊆Range : (f : A → B) → ∀ b → Image f ∋ b → b ∈ Range f
 Image⊆Range f b (eq a x) = a , (sym x)

 Range⊆Image : (f : A → B) → ∀ b → b ∈ Range f → Image f ∋ b
 Range⊆Image f b (a , x) = eq a (sym x)

 Imagef∋f : {f : A → B}{a : A} → Image f ∋ (f a)
 Imagef∋f = eq _ refl

 f∈range : {f : A → B}(a : A) → range f
 f∈range {f} a = (f a) , (a , refl)

\end{code}

An inhabitant of `Image f ∋ b` is a dependent pair `(a , p)`, where `a : A` and `p : b ≡ f a` is a proof that `f` maps `a` to `b`.  Since the proof that `b` belongs to the image of `f` is always accompanied by a witness `a : A`, we can actually *compute* a (pseudo)inverse of `f`. For convenience, we define this inverse function, which we call `Inv`, and which takes an arbitrary `b : B` and a (*witness*, *proof*)-pair, `(a , p) : Image f ∋ b`, and returns the witness `a`.

\begin{code}

 Inv : (f : A → B){b : B} → Image f ∋ b  →  A
 Inv f (eq a _) = a


 [_]⁻¹ : (f : A → B) → range f →  A
 [ f ]⁻¹ (_ , (a , _)) = a

\end{code}

We can prove that `Inv f` is the (range-restricted) *right-inverse* of `f`, as follows.

\begin{code}

 InvIsInverseʳ : {f : A → B}{b : B}(q : Image f ∋ b) → f(Inv f q) ≡ b
 InvIsInverseʳ (eq _ p) = sym p

 ⁻¹IsInverseʳ : {f : A → B}{bap : range f} → f ([ f ]⁻¹ bap) ≡ ∣ bap ∣
 ⁻¹IsInverseʳ {bap = (_ , (_ , p))} = p

\end{code}

Of course, the "range-restricted" qualifier is needed because `Inf f` is not defined outside the range of `f`.

In a certain sense, `Inv f` is also a (range-restricted) *left-inverse*.

\begin{code}

 InvIsInverseˡ : ∀ {f a} → Inv f {b = f a} Imagef∋f ≡ a
 InvIsInverseˡ = refl

 ⁻¹IsInverseˡ : ∀ {f a} → [ f ]⁻¹ (f∈range a) ≡ a
 ⁻¹IsInverseˡ = refl

\end{code}

--------------------------------------

<span style="float:left;">[← Base.Overture.Preliminaries](Base.Overture.Preliminaries.html)</span>
<span style="float:right;">[Base.Overture.Injective →](Base.Overture.Injective.html)</span>

{% include UALib.Links.md %}


