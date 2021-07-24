---
layout: default
title : Structures.Substructures.Substructures module (The Agda Universal Algebra Library)
date : 2021-07-23
author: [agda-algebras development team][]
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Structures.Substructures.Substructures where

-- imports from Agda and the Agda Standard Library
open import Agda.Primitive        using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type ; Setω to Typeω)
open import Data.Product          using ( _,_ ; Σ-syntax ; _×_ )
open import Relation.Binary       using ( REL )
open import Relation.Unary        using ( Pred ; _∈_ )

-- imports from agda-algebras ------------------------------------------------------
open import Overture.Preliminaries using ( ∣_∣ ; ∥_∥ )
open import Overture.Inverses      using ( IsInjective )
open import Structures.Basic       using ( signature ; structure ; sigl )
open import Structures.Homs        using ( hom )

open structure
open signature


private variable
 𝓞₀ 𝓥₀ 𝓞₁ 𝓥₁ ρ α ρᵃ β ρᵇ γ ρᶜ χ ι : Level
 𝐹 : signature 𝓞₀ 𝓥₀
 𝑅 : signature 𝓞₁ 𝓥₁

\end{code}


#### Substructures

\begin{code}

_≥s_  -- (alias for supstructure (aka parent structure; aka overstructure))
 _IsSupstructureOf_ : structure 𝐹 𝑅 {α}{ρᵃ} → structure 𝐹 𝑅 {β}{ρᵇ} → Type _
𝑨 IsSupstructureOf 𝑩 = Σ[ h ∈ hom 𝑩 𝑨 ] IsInjective ∣ h ∣

_≤s_  -- (alias for subalgebra relation))
 _IsSubstructureOf_ : structure 𝐹 𝑅 {α}{ρᵃ} → structure 𝐹 𝑅 {β}{ρᵇ} → Type _
𝑨 IsSubstructureOf 𝑩 = Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective ∣ h ∣

-- Syntactic sugar for sup/sub-algebra relations.
𝑨 ≥s 𝑩 = 𝑨 IsSupstructureOf 𝑩
𝑨 ≤s 𝑩 = 𝑨 IsSubstructureOf 𝑩

module _ {α ρᵃ β ρᵇ : Level}
         {𝐹 : signature 𝓞₀ 𝓥₀}
         {𝑅 : signature 𝓞₁ 𝓥₁}  where
 record SubstructureOf : Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ lsuc (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)) where
  field
   struc      : structure 𝐹 𝑅 {α}{ρᵃ}
   substruc   : structure 𝐹 𝑅 {β}{ρᵇ}
   issubstruc : substruc ≤s struc


 Substructure : structure 𝐹 𝑅 {α}{ρᵃ} → Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ α ⊔ ρᵃ ⊔ lsuc (β ⊔ ρᵇ))
 Substructure 𝑨 = Σ[ 𝑩 ∈ (structure 𝐹 𝑅 {β}{ρᵇ}) ] 𝑩 ≤s 𝑨

 -- usage note: for 𝑨 : structure 𝐹 𝑅 {α}{ρᵃ}, inhabitant of `Substructure 𝑨` is a pair
 --             `(𝑩 , p) : Substructure 𝑨`  providing
 --                                       - `𝑩 : structure 𝐹 𝑅 {β}{ρᵇ}` and
 --                                       - `p : 𝑩 ≤s 𝑨`, a proof that 𝑩 is a substructure of 𝐴.


 IsSubstructureREL : REL (structure 𝐹 𝑅 {α}{ρᵃ})(structure 𝐹 𝑅 {β}{ρᵇ}) ρ
  →                  Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ lsuc (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ))

 IsSubstructureREL R = ∀ {𝑨 : structure 𝐹 𝑅 {α}{ρᵃ}}{𝑩 : structure 𝐹 𝑅 {β}{ρᵇ}} → 𝑨 ≤s 𝑩

\end{code}

From now on we will use `𝑩 ≤s 𝑨` to express the assertion that `𝑩` is a subalgebra of `𝑨`.


#### Substructures of a class of algebras

Suppose `𝒦 : Pred (Algebra α 𝑆) γ` denotes a class of `𝑆`-algebras and `𝑩 : structure 𝐹 𝑅 {β}{ρᵇ}` denotes an arbitrary `𝑆`-algebra. Then we might wish to consider the assertion that `𝑩` is a subalgebra of an algebra in the class `𝒦`.  The next type we define allows us to express this assertion as `𝑩 IsSubstructureOfClass 𝒦`.

\begin{code}

 _≤c_
  _IsSubstructureOfClass_ : structure 𝐹 𝑅 {β}{ρᵇ} → Pred (structure 𝐹 𝑅 {α}{ρᵃ}) ρ → Type _
 𝑩 IsSubstructureOfClass 𝒦 = Σ[ 𝑨 ∈ structure 𝐹 𝑅 {α}{ρᵃ} ] ((𝑨 ∈ 𝒦) × (𝑩 ≤s 𝑨))

 𝑩 ≤c 𝒦 = 𝑩 IsSubstructureOfClass 𝒦

 record SubstructureOfClass : Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ lsuc (α ⊔ ρ ⊔ β ⊔ ρᵇ ⊔ ρᵃ))
  where
  field
   class : Pred (structure 𝐹 𝑅 {α}{ρᵃ}) ρ
   substruc : structure 𝐹 𝑅 {β}{ρᵇ}
   issubstrucofclass : substruc ≤c class


 record SubstructureOfClass' : Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ lsuc (α ⊔ ρ ⊔ β ⊔ ρᵇ ⊔ ρᵃ))
  where
  field
   class : Pred (structure 𝐹 𝑅 {α}{ρᵃ}) ρ
   classalgebra : structure 𝐹 𝑅 {α}{ρᵃ}
   isclassalgebra : classalgebra ∈ class
   subalgebra : structure 𝐹 𝑅 {β}{ρᵇ}
   issubalgebra : subalgebra ≤s classalgebra

 -- The collection of subalgebras of algebras in class 𝒦.
 SubstructuresOfClass : Pred (structure 𝐹 𝑅 {α}{ρᵃ}) ρ → Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ lsuc (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ) ⊔ ρ)
 SubstructuresOfClass 𝒦 = Σ[ 𝑩 ∈ structure _ _ ] 𝑩 ≤c 𝒦

\end{code}



------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

