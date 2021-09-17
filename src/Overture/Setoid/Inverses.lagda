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

module Overture.Setoid.Inverses
 {α ρᵃ β ρᵇ}{𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where

-- Imports from Agda and the Agda Standard Library --------------------
open import Agda.Primitive    using ( _⊔_ ) renaming ( Set to Type )
open import Function.Equality using ( Π ; _⟶_ )
import      Function.Definitions as FunctionDefinitions
import      Function.Structures as FunctionStructures
open import Data.Product      using ( _,_ )
open import Relation.Unary    using ( Pred ; _∈_ )

-- Imports from agda-algebras -----------------------------------------
open import Overture.Preliminaries using (∃-syntax)

open Setoid 𝑨 using () renaming (Carrier to A; _≈_ to _≈₁_)
open Setoid 𝑩 using ( sym ) renaming (Carrier to B; _≈_ to _≈₂_)
open FunctionDefinitions _≈₁_ _≈₂_
open FunctionStructures  _≈₁_ _≈₂_

\end{code}

We begin by defining an data type that represents the semantic concept of *inverse image* of a function.

\begin{code}

open Π

data Image_∋_ (f : 𝑨 ⟶ 𝑩) : B → Type (α ⊔ β ⊔ ρᵇ) where
 eq : {b : B} → (a : A) → b ≈₂ (f ⟨$⟩ a) → Image f ∋ b

open Image_∋_

Range : (𝑨 ⟶ 𝑩) → Pred B (α ⊔ ρᵇ)
Range f b = ∃[ a ∈ A ] (f ⟨$⟩ a) ≈₂ b

Image⊆Range : (f : 𝑨 ⟶ 𝑩) → ∀ b → Image f ∋ b → b ∈ Range f
Image⊆Range f b (eq a x) = a , (sym x)

Range⊆Image : (f : 𝑨 ⟶ 𝑩) → ∀ b → b ∈ Range f → Image f ∋ b
Range⊆Image f b (a , x) = eq a (sym x)

\end{code}

An inhabitant of `Image f ∋ b` is a dependent pair `(a , p)`, where `a : A` and `p : b ≡ f a` is a proof that `f` maps `a` to `b`.  Since the proof that `b` belongs to the image of `f` is always accompanied by a witness `a : A`, we can actually *compute* a (pseudo)inverse of `f`. For convenience, we define this inverse function, which we call `Inv`, and which takes an arbitrary `b : B` and a (*witness*, *proof*)-pair, `(a , p) : Image f ∋ b`, and returns the witness `a`.

\begin{code}

Inv : (f : 𝑨 ⟶ 𝑩){b : B} → Image f ∋ b  →  A
Inv _ (eq a _) = a

Inv' : (f : 𝑨 ⟶ 𝑩){b : B} → b ∈ Range f → A
Inv' _ (a , _) = a

\end{code}

We can prove that `Inv f` is the range-restricted right-inverse of `f`, as follows.

\begin{code}

InvIsInv : (f : 𝑨 ⟶ 𝑩){b : B}(q : Image f ∋ b) → (f ⟨$⟩ (Inv f q)) ≈₂ b
InvIsInv f (eq _ p) = sym p

\end{code}

Of course, the "range-restricted" qualifier is needed because `Inf f` is not defined outside the range of `f`.

--------------------------------------

<span style="float:left;">[← Overture.Setoid.Preliminaries](Overture.Setoid.Preliminaries.html)</span>
<span style="float:right;">[Overture.Setoid.Injective →](Overture.Setoid.Injective.html)</span>

{% include UALib.Links.md %}


