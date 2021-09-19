---
layout: default
title : "Overture.Setoid.Inverses module"
date : "2021-09-10"
author: "the agda-algebras development team"
---

### <a id="inverses-for-functions-on-setoids">Inverses for functions on setoids</a>

This is the [Overture.Setoid.Inverses][] module of the [agda-algebras][] library.
\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Relation.Binary using ( Setoid )

module Overture.FuncInverses
 {α ρᵃ β ρᵇ}{𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where

-- Imports from Agda and the Agda Standard Library --------------------
open import Agda.Primitive    using ( _⊔_ ) renaming ( Set to Type )
open import Function.Bundles as FB using ( Func )
open import Data.Product      using ( _,_ )
open import Relation.Unary    using ( Pred ; _∈_ )

-- Imports from agda-algebras -----------------------------------------
open import Overture.Preliminaries using (∃-syntax)

open Setoid 𝑨 using () renaming (Carrier to A; _≈_ to _≈₁_)
open Setoid 𝑩 using ( sym ) renaming (Carrier to B; _≈_ to _≈₂_)

\end{code}

We begin by defining an data type that represents the semantic concept of *inverse image* of a function.

\begin{code}

open Func {a = α}{ρᵃ}{β}{ρᵇ}{From = 𝑨}{To = 𝑩}

data Image_∋_ (F : Func 𝑨 𝑩) : B → Type (α ⊔ β ⊔ ρᵇ) where
 eq : {b : B} → (a : A) → b ≈₂ ((f F) a) → Image F ∋ b

open Image_∋_

Range : (Func 𝑨 𝑩) → Pred B (α ⊔ ρᵇ)
Range F b = ∃[ a ∈ A ] ((f F) a) ≈₂ b

Image⊆Range : ∀ {F b} → Image F ∋ b → b ∈ Range F
Image⊆Range (eq a x) = a , (sym x)

Range⊆Image : ∀ {F b} → b ∈ Range F → Image F ∋ b
Range⊆Image (a , x) = eq a (sym x)

\end{code}

An inhabitant of `Image f ∋ b` is a dependent pair `(a , p)`, where `a : A` and `p : b ≡ f a` is a proof that `f` maps `a` to `b`.  Since the proof that `b` belongs to the image of `f` is always accompanied by a witness `a : A`, we can actually *compute* a (pseudo)inverse of `f`. For convenience, we define this inverse function, which we call `Inv`, and which takes an arbitrary `b : B` and a (*witness*, *proof*)-pair, `(a , p) : Image f ∋ b`, and returns the witness `a`.

\begin{code}

Inv : (F : Func 𝑨 𝑩){b : B} → Image F ∋ b → A
Inv _ (eq a _) = a

Inv' : (F : Func 𝑨 𝑩){b : B} → b ∈ Range F → A
Inv' _ (a , _) = a

\end{code}

We can prove that `Inv f` is the range-restricted right-inverse of `f`, as follows.

\begin{code}

InvIsInv : (F : Func 𝑨 𝑩){b : B}(q : Image F ∋ b) → ((f F) (Inv F q)) ≈₂ b
InvIsInv f (eq _ p) = sym p

\end{code}

Of course, the "range-restricted" qualifier is needed because `Inf f` is not defined outside the range of `f`.

--------------------------------------

<span style="float:left;">[← Overture.Setoid.Preliminaries](Overture.Setoid.Preliminaries.html)</span>
<span style="float:right;">[Overture.Setoid.Injective →](Overture.Setoid.Injective.html)</span>

{% include UALib.Links.md %}


