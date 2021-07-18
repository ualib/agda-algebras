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
open import Agda.Primitive         using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type )
open import Agda.Builtin.Equality   using    ( _≡_ ; refl )
open import Data.Product            using    ( _,_ ; Σ-syntax ; _×_ )
open import Function.Base           using    ( id )
open import Function.Bundles        using    ( Injection )
open import Relation.Binary         using    ( Setoid ; REL )
open import Relation.Unary          using    ( Pred ; _∈_ ; _⊆_ )

-- -- -- -- imports from agda-algebras ------------------------------------------------------
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

 _≥s_  -- (alias for supalgebra (aka overalgebra))
  _IsSupalgebraOf_ : SetoidAlgebra α ρᵃ → SetoidAlgebra β ρᵇ → Type _
 𝑨 IsSupalgebraOf 𝑩 = Σ[ h ∈ hom 𝑩 𝑨 ] IsInjective ∣ h ∣

 _≤s_  -- (alias for subalgebra relation))
  _IsSubalgebraOf_ : SetoidAlgebra α ρᵃ → SetoidAlgebra β ρᵇ → Type _
 𝑨 IsSubalgebraOf 𝑩 = Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective ∣ h ∣

 -- Syntactic sugar for sup/sub-algebra relations.
 𝑨 ≥s 𝑩 = 𝑨 IsSupalgebraOf 𝑩
 𝑨 ≤s 𝑩 = 𝑨 IsSubalgebraOf 𝑩

 open _≅_
 ≅→≤s : {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ} → 𝑨 ≅ 𝑩 → 𝑨 ≤s 𝑩
 ≅→≤s φ = (to φ) , ≅toInjective φ

 ≅→≥s : {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ} → 𝑨 ≅ 𝑩 → 𝑨 ≥s 𝑩
 ≅→≥s φ = (from φ) , ≅fromInjective φ

 record SubalgebraOf : Type (ov (α ⊔ β ⊔ ρ ⊔ ρᵃ ⊔ ρᵇ)) where
  field
   algebra : SetoidAlgebra α ρᵃ
   subalgebra : SetoidAlgebra β ρᵇ
   issubalgebra : subalgebra ≤s algebra


 Subalgebra : SetoidAlgebra α ρᵃ → {β ρᵇ : Level} → Type _
 Subalgebra 𝑨 {β}{ρᵇ} = Σ[ 𝑩 ∈ (SetoidAlgebra β ρᵇ) ] 𝑩 ≤s 𝑨

 -- usage note: for 𝑨 : SetoidAlgebra α ρᵃ, inhabitant of `Subalgebra 𝑨` is a pair
 --             `(𝑩 , p) : Subalgebra 𝑨`  providing
 --                                       - `𝑩 : SetoidAlgebra β ρᵇ` and
 --                                       - `p : 𝑩 ≤s 𝑨`, a proof that 𝑩 is a subalgebra of 𝐴.


 IsSubalgebraREL : {α ρᵃ β ρᵇ : Level} → REL (SetoidAlgebra α ρᵃ)(SetoidAlgebra β ρᵇ) ρ → Type _
 IsSubalgebraREL {α}{ρᵃ}{β}{ρᵇ} R = ∀ {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ} → 𝑨 ≤s 𝑩

 record SubalgebraREL(R : REL (SetoidAlgebra β ρᵇ)(SetoidAlgebra α ρᵃ) ρ) : Type (ov (α ⊔ β ⊔ ρ ⊔ ρᵃ ⊔ ρᵇ))
  where
  field isSubalgebraREL : IsSubalgebraREL R


\end{code}

From now on we will use `𝑩 ≤s 𝑨` to express the assertion that `𝑩` is a subalgebra of `𝑨`.


#### Subalgebras of a class of algebras

Suppose `𝒦 : Pred (Algebra α 𝑆) γ` denotes a class of `𝑆`-algebras and `𝑩 : SetoidAlgebra β ρᵇ` denotes an arbitrary `𝑆`-algebra. Then we might wish to consider the assertion that `𝑩` is a subalgebra of an algebra in the class `𝒦`.  The next type we define allows us to express this assertion as `𝑩 IsSubalgebraOfClass 𝒦`.

\begin{code}

module _ where

 private variable
  α ρᵃ β ρᵇ : Level

 _≤c_
  _IsSubalgebraOfClass_ : SetoidAlgebra β ρᵇ → Pred (SetoidAlgebra α ρᵃ) ρ → Type _
 𝑩 IsSubalgebraOfClass 𝒦 = Σ[ 𝑨 ∈ SetoidAlgebra _ _ ] ((𝑨 ∈ 𝒦) × (𝑩 ≤s 𝑨))

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
   issubalgebra : subalgebra ≤s classalgebra

 -- The collection of subalgebras of algebras in class 𝒦.
 SubalgebrasOfClass : Pred (SetoidAlgebra α ρᵃ) ρ → {β ρᵇ : Level} → Type _
 SubalgebrasOfClass 𝒦 {β}{ρᵇ} = Σ[ 𝑩 ∈ SetoidAlgebra β ρᵇ ] 𝑩 ≤c 𝒦

\end{code}


#### Subalgebra lemmas

The subalgebra relation is a *preorder*; i.e., it is a reflexive, transitive binary relation.

\begin{code}


private variable α ρᵃ β ρᵇ γ ρᶜ : Level

≤s-refl : {𝑨 𝑩 : SetoidAlgebra α ρᵃ} → 𝑨 ≅ 𝑩 → 𝑨 ≤s 𝑩
≤s-refl {𝑨 = 𝑨}{𝑩} A≅B = ≅→≤s A≅B

≥s-refl : {𝑨 𝑩 : SetoidAlgebra α ρᵃ} → 𝑨 ≅ 𝑩 → 𝑨 ≥s 𝑩
≥s-refl {𝑨 = 𝑨}{𝑩} A≅B = ≅→≤s (≅-sym A≅B)

≤s-refl' : {𝑨 : SetoidAlgebra α ρᵃ} → 𝑨 ≤s 𝑨
≤s-refl' {𝑨 = 𝑨} = (id , λ f a → refl) , Injection.injective id-is-injective


≤s-trans : (𝑨 : SetoidAlgebra α ρᵃ){𝑩 : SetoidAlgebra β ρᵇ}(𝑪 : SetoidAlgebra γ ρᶜ)
  →        𝑨 ≤s 𝑩 → 𝑩 ≤s 𝑪 → 𝑨 ≤s 𝑪

≤s-trans 𝑨 {𝑩} 𝑪 A≤B B≤C = (∘-hom 𝑨 𝑩 𝑪 ∣ A≤B ∣ ∣ B≤C ∣ ) , Goal
 where
 Goal : IsInjective ∣ (∘-hom 𝑨 𝑩 𝑪 ∣ A≤B ∣ ∣ B≤C ∣) ∣
 Goal = ∘-injective ∥ A≤B ∥ ∥ B≤C ∥

≥s-trans : (𝑨 : SetoidAlgebra α ρᵃ){𝑩 : SetoidAlgebra β ρᵇ}(𝑪 : SetoidAlgebra γ ρᶜ)
  →        𝑨 ≥s 𝑩 → 𝑩 ≥s 𝑪 → 𝑨 ≥s 𝑪
≥s-trans 𝑨 {𝑩} 𝑪 A≥B B≥C = ≤s-trans 𝑪 {𝑩} 𝑨 B≥C A≥B


module _ {α ρᵃ ρ : Level} where

 open import Relation.Binary.Structures {a = ov(α ⊔ ρᵃ)}{ℓ = (𝓞 ⊔ 𝓥 ⊔ α)} (_≅_ {α}{ρᵃ}{α}{ρᵃ})

 open IsPreorder
 ≤s-preorder : IsPreorder _≤s_
 isEquivalence ≤s-preorder = record { refl = ≅-refl ; sym = ≅-sym ; trans = ≅-trans }
 reflexive ≤s-preorder = ≤s-refl
 trans ≤s-preorder {𝑨}{𝑩}{𝑪} A≤B B≤C = ≤s-trans 𝑨 {𝑩} 𝑪 A≤B B≤C



open _≅_

module _ (𝑨 : SetoidAlgebra α ρᵃ){𝑩 : SetoidAlgebra β ρᵇ}(𝑪 : SetoidAlgebra γ ρᶜ) where

 A≥B→B≅C→A≥C : 𝑨 ≥s 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≥s 𝑪
 A≥B→B≅C→A≥C A≥B B≅C  = ≥s-trans 𝑨 {𝑩} 𝑪 A≥B (≅→≥s B≅C)

 A≤B→B≅C→A≤C : 𝑨 ≤s 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≤s 𝑪
 A≤B→B≅C→A≤C A≤B B≅C = ≤s-trans 𝑨{𝑩} 𝑪 A≤B (≅→≤s B≅C)

 A≅B→B≥C→A≥C : 𝑨 ≅ 𝑩 → 𝑩 ≥s 𝑪 → 𝑨 ≥s 𝑪

 A≅B→B≥C→A≥C A≅B B≥C = ≥s-trans 𝑨{𝑩}𝑪 (≅→≥s A≅B) B≥C

 A≅B→B≤C→A≤C : 𝑨 ≅ 𝑩 → 𝑩 ≤s 𝑪 → 𝑨 ≤s 𝑪
 A≅B→B≤C→A≤C A≅B B≤C = ≤s-trans 𝑨{𝑩}𝑪 (≅→≤s A≅B) B≤C


≤s-TRANS-≅ : (𝑨 : SetoidAlgebra α ρᵃ){𝑩 : SetoidAlgebra β ρᵇ}(𝑪 : SetoidAlgebra γ ρᶜ)
 →          𝑨 ≤s 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≤s 𝑪
≤s-TRANS-≅ 𝑨 {𝑩} 𝑪 (h , hinj) B≅C = (∘-hom 𝑨 𝑩 𝑪 h (to B≅C)) , ∘-injective hinj (≅toInjective B≅C)

≤s-mono : (𝑩 : SetoidAlgebra β ρᵇ){𝒦 𝒦' : Pred (SetoidAlgebra α ρᵃ) γ}
 →        𝒦 ⊆ 𝒦' → 𝑩 IsSubalgebraOfClass 𝒦 → 𝑩 IsSubalgebraOfClass 𝒦'

≤s-mono 𝑩 KK' (𝑨 , (KA , B≤A)) = 𝑨 , ((KK' KA) , B≤A)

\end{code}


#### Lifts of subalgebras

\begin{code}

module _ {𝒦 : Pred (SetoidAlgebra α ρᵃ)(ov α)}{𝑩 : SetoidAlgebra β ρᵇ}{ℓ : Level} where

 Lift-is-sub : 𝑩 IsSubalgebraOfClass 𝒦 → (Lift-SetoidAlg 𝑩 ℓ) IsSubalgebraOfClass 𝒦
 Lift-is-sub (𝑨 , (KA , B≤A)) = 𝑨 , (KA , A≥B→B≅C→A≥C 𝑨 (Lift-SetoidAlg 𝑩 ℓ) B≤A Lift-≅)

≤s-Lift : (𝑨 : SetoidAlgebra α ρᵃ){𝑩 : SetoidAlgebra β ρᵇ}{ℓ : Level} → 𝑨 ≤s 𝑩 → 𝑨 ≤s Lift-SetoidAlg 𝑩 ℓ
≤s-Lift 𝑨 {𝑩}{ℓ} A≤sB = A≤B→B≅C→A≤C 𝑨 (Lift-SetoidAlg 𝑩 ℓ) A≤sB Lift-≅

≥s-Lift : (𝑨 : SetoidAlgebra α ρᵃ){𝑩 : SetoidAlgebra β ρᵇ}{ℓ : Level} → 𝑨 ≥s 𝑩 → 𝑨 ≥s Lift-SetoidAlg 𝑩 ℓ
≥s-Lift 𝑨 {𝑩}{ℓ} A≥sB = A≥B→B≅C→A≥C 𝑨 (Lift-SetoidAlg 𝑩 ℓ) A≥sB Lift-≅

Lift-≤s-Lift : {𝑨 : SetoidAlgebra α ρᵃ}(ℓᵃ : Level){𝑩 : SetoidAlgebra β ρᵇ}(ℓᵇ : Level)
 →             𝑨 ≤s 𝑩 → Lift-SetoidAlg 𝑨 ℓᵃ ≤s Lift-SetoidAlg 𝑩 ℓᵇ
Lift-≤s-Lift {𝑨 = 𝑨} ℓᵃ {𝑩} ℓᵇ A≤sB = ≥s-Lift (Lift-SetoidAlg 𝑩 ℓᵇ){𝑨} (≤s-Lift 𝑨{𝑩} A≤sB)

\end{code}

------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

