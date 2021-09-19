---
layout: default
title : "Subalgebras.Setoid.Subalgebras module (The Agda Universal Algebra Library)"
date : "2021-07-17"
author: "agda-algebras development team"
---

#### <a id="subalgebras-of SetoidAlgebras">Subalgebras of setoid algebras</a>

This is the [Subalgebras.Setoid.Subalgebras][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Subalgebras.Setoid.Subalgebras {𝑆 : Signature 𝓞 𝓥} where

-- imports from Agda and the Agda Standard Library -------------------------------------------------
open import Agda.Primitive   using ( Level ; _⊔_ ) renaming ( Set to Type )
open import Data.Product     using ( _,_ ; Σ-syntax ) renaming ( _×_ to _∧_ )
open import Relation.Binary  using ( REL )
open import Relation.Unary   using ( Pred ; _∈_ )

-- Imports from the Agda Universal Algebra Library --------------------------------------------------
open import Overture.Preliminaries           using ( ∣_∣ )
open import Overture.Func.Injective          using ( IsInjective )
open import Algebras.Func.Basic      {𝑆 = 𝑆} using ( SetoidAlgebra ; ov )
open import Homomorphisms.Func.Basic {𝑆 = 𝑆} using ( hom )

private variable
 α ρᵃ β ρᵇ ℓ : Level

_≥_  -- (alias for supalgebra (aka overalgebra))
 _IsSupalgebraOf_ : SetoidAlgebra α ρᵃ → SetoidAlgebra β ρᵇ → Type _
𝑨 IsSupalgebraOf 𝑩 = Σ[ h ∈ hom 𝑩 𝑨 ] IsInjective ∣ h ∣

_≤_  -- (alias for subalgebra relation))
 _IsSubalgebraOf_ : SetoidAlgebra α ρᵃ → SetoidAlgebra β ρᵇ → Type _
𝑨 IsSubalgebraOf 𝑩 = Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective ∣ h ∣

-- Syntactic sugar for sup/sub-algebra relations.
𝑨 ≥ 𝑩 = 𝑨 IsSupalgebraOf 𝑩
𝑨 ≤ 𝑩 = 𝑨 IsSubalgebraOf 𝑩


record SubalgebraOf : Type (ov (α ⊔ β ⊔ ρᵃ ⊔ ρᵇ)) where
 field
  algebra : SetoidAlgebra α ρᵃ
  subalgebra : SetoidAlgebra β ρᵇ
  issubalgebra : subalgebra ≤ algebra


Subalgebra : SetoidAlgebra α ρᵃ → {β ρᵇ : Level} → Type _
Subalgebra 𝑨 {β}{ρᵇ} = Σ[ 𝑩 ∈ (SetoidAlgebra β ρᵇ) ] 𝑩 ≤ 𝑨

{- usage note: for 𝑨 : SetoidAlgebra α ρᵃ, inhabitant of `Subalgebra 𝑨` is a pair
               `(𝑩 , p) : Subalgebra 𝑨`  providing
                                         - `𝑩 : SetoidAlgebra β ρᵇ` and
                                         - `p : 𝑩 ≤ 𝑨`, a proof that 𝑩 is a subalgebra of 𝐴. -}


IsSubalgebraREL : {α ρᵃ β ρᵇ : Level} → REL (SetoidAlgebra α ρᵃ)(SetoidAlgebra β ρᵇ) ℓ → Type _
IsSubalgebraREL {α}{ρᵃ}{β}{ρᵇ} R = ∀ {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ} → 𝑨 ≤ 𝑩

record SubalgebraREL(R : REL (SetoidAlgebra β ρᵇ)(SetoidAlgebra α ρᵃ) ℓ) : Type (ov (α ⊔ β ⊔ ρᵇ ⊔ ℓ))
 where
 field isSubalgebraREL : IsSubalgebraREL R


\end{code}

From now on we will use `𝑩 ≤ 𝑨` to express the assertion that `𝑩` is a subalgebra of `𝑨`.


#### <a id="subalgebras-of-classes-of-algebras">Subalgebras of classes of setoid algebras</a>

Suppose `𝒦 : Pred (Algebra α 𝑆) γ` denotes a class of `𝑆`-algebras and `𝑩 : SetoidAlgebra β ρᵇ` denotes an arbitrary `𝑆`-algebra. Then we might wish to consider the assertion that `𝑩` is a subalgebra of an algebra in the class `𝒦`.  The next type we define allows us to express this assertion as `𝑩 IsSubalgebraOfClass 𝒦`.

\begin{code}

_≤c_
 _IsSubalgebraOfClass_ : SetoidAlgebra β ρᵇ → Pred (SetoidAlgebra α ρᵃ) ℓ → Type _
𝑩 IsSubalgebraOfClass 𝒦 = Σ[ 𝑨 ∈ SetoidAlgebra _ _ ] ((𝑨 ∈ 𝒦) ∧ (𝑩 ≤ 𝑨))

𝑩 ≤c 𝒦 = 𝑩 IsSubalgebraOfClass 𝒦

record SubalgebraOfClass : Type (ov (α ⊔ β ⊔ ρᵃ ⊔ ρᵇ ⊔ ℓ))
 where
 field
  class : Pred (SetoidAlgebra α ρᵃ) ℓ
  subalgebra : SetoidAlgebra β ρᵇ
  issubalgebraofclass : subalgebra ≤c class


record SubalgebraOfClass' : Type (ov (α ⊔ β ⊔ ρᵃ ⊔ ρᵇ ⊔ ℓ))
 where
 field
  class : Pred (SetoidAlgebra α ρᵃ) ℓ
  classalgebra : SetoidAlgebra α ρᵃ
  isclassalgebra : classalgebra ∈ class
  subalgebra : SetoidAlgebra β ρᵇ
  issubalgebra : subalgebra ≤ classalgebra

-- The collection of subalgebras of algebras in class 𝒦.
SubalgebrasOfClass : Pred (SetoidAlgebra α ρᵃ) ℓ → {β ρᵇ : Level} → Type _
SubalgebrasOfClass 𝒦 {β}{ρᵇ} = Σ[ 𝑩 ∈ SetoidAlgebra β ρᵇ ] 𝑩 ≤c 𝒦

\end{code}

---------------------------------

<span style="float:left;">[← Subalgebras.Setoid.Subuniverses](Subalgebras.Setoid.Subuniverses.html)</span>
<span style="float:right;">[Subalgebras.Setoid.Properties →](Subalgebras.Setoid.Properties.html)</span>

{% include UALib.Links.md %}
