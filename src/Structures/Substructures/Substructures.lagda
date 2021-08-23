---
layout: default
title : Structures.Substructures.Substructures module (The Agda Universal Algebra Library)
date : 2021-07-23
author: [agda-algebras development team][]
---

#### Substructures


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Structures.Substructures.Substructures where

-- imports from Agda and the Agda Standard Library
open import Agda.Primitive  using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type )
open import Data.Product    using ( _,_ ; Σ-syntax ; _×_ )
open import Relation.Binary using ( REL )
open import Relation.Unary  using ( Pred ; _∈_ )

-- imports from agda-algebras ------------------------------------------------------
open import Overture.Preliminaries using ( ∣_∣ ; ∥_∥ )
open import Overture.Inverses      using ( IsInjective )
open import Relations.Discrete     using ( PredType )
open import Structures.Basic       using ( signature ; structure ; sigl )
open import Structures.Homs        using ( hom )

open structure
open signature


private variable
 𝓞₀ 𝓥₀ 𝓞₁ 𝓥₁ ρ α ρᵃ β ρᵇ γ ρᶜ χ ι : Level
 𝐹 : signature 𝓞₀ 𝓥₀
 𝑅 : signature 𝓞₁ 𝓥₁

_≥s_  -- (alias for supstructure (aka parent structure; aka overstructure))
 _IsSupstructureOf_ : structure 𝐹 𝑅 {α}{ρᵃ} → structure 𝐹 𝑅 {β}{ρᵇ}
  →                   Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)

𝑨 IsSupstructureOf 𝑩 = Σ[ h ∈ hom 𝑩 𝑨 ] IsInjective ∣ h ∣


_≤s_  -- (alias for subalgebra relation))
 _IsSubstructureOf_ : structure 𝐹 𝑅 {α}{ρᵃ} → structure 𝐹 𝑅 {β}{ρᵇ}
  →                   Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ )

𝑨 IsSubstructureOf 𝑩 = Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective ∣ h ∣

-- Syntactic sugar for sup/sub-algebra relations.
𝑨 ≥s 𝑩 = 𝑨 IsSupstructureOf 𝑩
𝑨 ≤s 𝑩 = 𝑨 IsSubstructureOf 𝑩


record SubstructureOf : Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ lsuc (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)) where
 field
  struc      : structure 𝐹 𝑅 {α}{ρᵃ}
  substruc   : structure 𝐹 𝑅 {β}{ρᵇ}
  issubstruc : substruc ≤s struc



module _ {𝐹 : signature 𝓞₀ 𝓥₀}
         {𝑅 : signature 𝓞₁ 𝓥₁}  where

 Substructure : structure 𝐹 𝑅 {α}{ρᵃ} → {β ρᵇ : Level}
  →             Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ α ⊔ ρᵃ ⊔ lsuc (β ⊔ ρᵇ))

 Substructure 𝑨 {β}{ρᵇ} = Σ[ 𝑩 ∈ (structure 𝐹 𝑅 {β}{ρᵇ}) ] 𝑩 ≤s 𝑨

 {- For 𝑨 : structure 𝐹 𝑅 {α}{ρᵃ}, inhabitant of `Substructure 𝑨` is
    a pair `(𝑩 , p) : Substructure 𝑨`  providing
    + a structure, `𝑩 : structure 𝐹 𝑅 {β}{ρᵇ}`, and
    + a proof, `p : 𝑩 ≤s 𝑨`, that 𝑩 is a substructure of 𝐴. -}


 IsSubstructureREL : ∀ {α}{ρᵃ}{β}{ρᵇ} → REL (structure 𝐹 𝑅 {α}{ρᵃ})(structure 𝐹 𝑅 {β}{ρᵇ}) ρ
  →                  Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ lsuc (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ))

 IsSubstructureREL {α = α}{ρᵃ}{β}{ρᵇ} R = ∀ {𝑨 : structure 𝐹 𝑅 {α}{ρᵃ}}{𝑩 : structure 𝐹 𝑅 {β}{ρᵇ}} → 𝑨 ≤s 𝑩

\end{code}

From now on we will use `𝑩 ≤s 𝑨` to express the assertion that `𝑩` is a subalgebra of `𝑨`.

#### Substructures of a class of algebras

Suppose `𝒦 : Pred (Algebra α 𝑆) γ` denotes a class of `𝑆`-algebras and `𝑩 : structure 𝐹 𝑅 {β}{ρᵇ}` denotes an arbitrary `𝑆`-algebra. Then we might wish to consider the assertion that `𝑩` is a subalgebra of an algebra in the class `𝒦`.  The next type we define allows us to express this assertion as `𝑩 IsSubstructureOfClass 𝒦`.

\begin{code}

 _≤c_  -- (alias for substructure-of-class relation)
  _IsSubstructureOfClass_ : structure 𝐹 𝑅 {β}{ρᵇ} → Pred (structure 𝐹 𝑅 {α}{ρᵃ}) ρ
   →                        Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ lsuc (α ⊔ ρᵃ) ⊔ β ⊔ ρᵇ ⊔ ρ)

 𝑩 IsSubstructureOfClass 𝒦 = Σ[ 𝑨 ∈ PredType 𝒦 ] ((𝑨 ∈ 𝒦) × (𝑩 ≤s 𝑨))

 𝑩 ≤c 𝒦 = 𝑩 IsSubstructureOfClass 𝒦

 record SubstructureOfClass : Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ lsuc (α ⊔ ρ ⊔ β ⊔ ρᵇ ⊔ ρᵃ)) where
  field
   class : Pred (structure 𝐹 𝑅 {α}{ρᵃ}) ρ
   substruc : structure 𝐹 𝑅 {β}{ρᵇ}
   issubstrucofclass : substruc ≤c class


 record SubstructureOfClass' : Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ lsuc (α ⊔ ρ ⊔ β ⊔ ρᵇ ⊔ ρᵃ)) where
  field
   class : Pred (structure 𝐹 𝑅 {α}{ρᵃ}) ρ
   classalgebra : structure 𝐹 𝑅 {α}{ρᵃ}
   isclassalgebra : classalgebra ∈ class
   subalgebra : structure 𝐹 𝑅 {β}{ρᵇ}
   issubalgebra : subalgebra ≤s classalgebra

 -- The collection of subalgebras of algebras in class 𝒦.
 SubstructuresOfClass : Pred (structure 𝐹 𝑅 {α}{ρᵃ}) ρ → {β ρᵇ : Level}
  →                     Type (sigl 𝐹 ⊔ sigl 𝑅 ⊔ lsuc (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ) ⊔ ρ)

 SubstructuresOfClass 𝒦 {β}{ρᵇ} = Σ[ 𝑩 ∈ structure 𝐹 𝑅 {β}{ρᵇ} ] 𝑩 ≤c 𝒦

\end{code}


--------------------------------

<br>
<br>

[← Structures.Substructures.Basic](Structures.Substructures.Basic.html)
<span style="float:right;">[Structures.Sigma →](Structures.Sigma.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

