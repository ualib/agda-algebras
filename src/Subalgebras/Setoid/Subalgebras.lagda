---
layout: default
title : Subalgebras.Setoid.Subalgebras module (The Agda Universal Algebra Library)
date : 2021-07-17
author: [agda-algebras development team][]
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Subalgebras.Setoid.Subalgebras {𝑆 : Signature 𝓞 𝓥} where

-- imports from Agda and the Agda Standard Library
open import Agda.Primitive   using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type )
open import Data.Product     using ( _,_ ; Σ-syntax ; _×_ )
open import Function.Base    using ( id )
open import Function.Bundles using ( Injection )
open import Relation.Binary  using ( Setoid ; REL )
open import Relation.Unary   using ( Pred ; _∈_ ; _⊆_ )

-- imports from agda-algebras ------------------------------------------------------
open import Overture.Preliminaries                    using ( ∣_∣ ; ∥_∥ )
open import Overture.Inverses                         using ( IsInjective ; id-is-injective ; ∘-injective )
open import Algebras.Setoid.Basic             {𝑆 = 𝑆} using ( SetoidAlgebra ; Lift-SetoidAlg )
open import Algebras.Products                 {𝑆 = 𝑆} using ( ov )
open import Homomorphisms.Setoid.Basic        {𝑆 = 𝑆} using ( hom ; ∘-hom )
open import Homomorphisms.Setoid.Isomorphisms {𝑆 = 𝑆} using ( _≅_ ; ≅toInjective ; ≅fromInjective
                                                            ;  ≅-sym ; ≅-refl ; ≅-trans ; Lift-≅ )

private variable ρ : Level

\end{code}


#### Subalgebras of SetoidAlgebras

\begin{code}
module _ where

 private variable
  α ρᵃ β ρᵇ : Level

 _≥_  -- (alias for supalgebra (aka overalgebra))
  _IsSupalgebraOf_ : SetoidAlgebra α ρᵃ → SetoidAlgebra β ρᵇ → Type _
 𝑨 IsSupalgebraOf 𝑩 = Σ[ h ∈ hom 𝑩 𝑨 ] IsInjective ∣ h ∣

 _≤_  -- (alias for subalgebra relation))
  _IsSubalgebraOf_ : SetoidAlgebra α ρᵃ → SetoidAlgebra β ρᵇ → Type _
 𝑨 IsSubalgebraOf 𝑩 = Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective ∣ h ∣

 -- Syntactic sugar for sup/sub-algebra relations.
 𝑨 ≥ 𝑩 = 𝑨 IsSupalgebraOf 𝑩
 𝑨 ≤ 𝑩 = 𝑨 IsSubalgebraOf 𝑩


 record SubalgebraOf : Type (ov (α ⊔ β ⊔ ρ ⊔ ρᵃ ⊔ ρᵇ)) where
  field
   algebra : SetoidAlgebra α ρᵃ
   subalgebra : SetoidAlgebra β ρᵇ
   issubalgebra : subalgebra ≤ algebra


 Subalgebra : SetoidAlgebra α ρᵃ → {β ρᵇ : Level} → Type _
 Subalgebra 𝑨 {β}{ρᵇ} = Σ[ 𝑩 ∈ (SetoidAlgebra β ρᵇ) ] 𝑩 ≤ 𝑨

 -- usage note: for 𝑨 : SetoidAlgebra α ρᵃ, inhabitant of `Subalgebra 𝑨` is a pair
 --             `(𝑩 , p) : Subalgebra 𝑨`  providing
 --                                       - `𝑩 : SetoidAlgebra β ρᵇ` and
 --                                       - `p : 𝑩 ≤ 𝑨`, a proof that 𝑩 is a subalgebra of 𝐴.


 IsSubalgebraREL : {α ρᵃ β ρᵇ : Level} → REL (SetoidAlgebra α ρᵃ)(SetoidAlgebra β ρᵇ) ρ → Type _
 IsSubalgebraREL {α}{ρᵃ}{β}{ρᵇ} R = ∀ {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ} → 𝑨 ≤ 𝑩

 record SubalgebraREL(R : REL (SetoidAlgebra β ρᵇ)(SetoidAlgebra α ρᵃ) ρ) : Type (ov (α ⊔ β ⊔ ρ ⊔ ρᵃ ⊔ ρᵇ))
  where
  field isSubalgebraREL : IsSubalgebraREL R


\end{code}

From now on we will use `𝑩 ≤ 𝑨` to express the assertion that `𝑩` is a subalgebra of `𝑨`.


#### Subalgebras of a class of algebras

Suppose `𝒦 : Pred (Algebra α 𝑆) γ` denotes a class of `𝑆`-algebras and `𝑩 : SetoidAlgebra β ρᵇ` denotes an arbitrary `𝑆`-algebra. Then we might wish to consider the assertion that `𝑩` is a subalgebra of an algebra in the class `𝒦`.  The next type we define allows us to express this assertion as `𝑩 IsSubalgebraOfClass 𝒦`.

\begin{code}

module _ where

 private variable
  α ρᵃ β ρᵇ : Level

 _≤c_
  _IsSubalgebraOfClass_ : SetoidAlgebra β ρᵇ → Pred (SetoidAlgebra α ρᵃ) ρ → Type _
 𝑩 IsSubalgebraOfClass 𝒦 = Σ[ 𝑨 ∈ SetoidAlgebra _ _ ] ((𝑨 ∈ 𝒦) × (𝑩 ≤ 𝑨))

 𝑩 ≤c 𝒦 = 𝑩 IsSubalgebraOfClass 𝒦

 record SubalgebraOfClass : Type (ov (α ⊔ β ⊔ ρ ⊔ ρᵃ ⊔ ρᵇ))
  where
  field
   class : Pred (SetoidAlgebra α ρᵃ) ρ
   subalgebra : SetoidAlgebra β ρᵇ
   issubalgebraofclass : subalgebra ≤c class


 record SubalgebraOfClass' : Type (ov (α ⊔ β ⊔ ρ ⊔ ρᵃ ⊔ ρᵇ))
  where
  field
   class : Pred (SetoidAlgebra α ρᵃ) ρ
   classalgebra : SetoidAlgebra α ρᵃ
   isclassalgebra : classalgebra ∈ class
   subalgebra : SetoidAlgebra β ρᵇ
   issubalgebra : subalgebra ≤ classalgebra

 -- The collection of subalgebras of algebras in class 𝒦.
 SubalgebrasOfClass : Pred (SetoidAlgebra α ρᵃ) ρ → {β ρᵇ : Level} → Type _
 SubalgebrasOfClass 𝒦 {β}{ρᵇ} = Σ[ 𝑩 ∈ SetoidAlgebra β ρᵇ ] 𝑩 ≤c 𝒦

\end{code}



---------------------------------

<br>
<br>

[← Subalgebras.Setoid.Subuniverses](Subalgebras.Setoid.Subuniverses.html)
<span style="float:right;">[Subalgebras.Setoid.Properties →](Subalgebras.Setoid.Properties.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

