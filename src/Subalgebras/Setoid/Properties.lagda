---
layout: default
title : Subalgebras.Setoid.Properties module (The Agda Universal Algebra Library)
date : 2021-07-18
author: [agda-algebras development team][]
---

#### <a id="properties-of-the-subalgebra-relation">Properties of the Subalgebra Relation</a>

This is the [Subalgebras.Setoid.Properties][] module of the [Agda Universal Algebra Library][].


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Subalgebras.Setoid.Properties {𝑆 : Signature 𝓞 𝓥} where

-- imports from Agda and the Agda Standard Library
open import Agda.Primitive   using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type )
open import Data.Product     using ( _,_ )
open import Function.Base    using ( id )
open import Function.Bundles using ( Injection )
open import Relation.Binary  using ( Setoid ; REL )
open import Relation.Unary   using ( Pred ; _⊆_ )
open import Relation.Binary.PropositionalEquality
                             using ( refl )

-- imports from agda-algebras ------------------------------------------------------
open import Overture.Preliminaries                    using ( ∣_∣ ; ∥_∥ )
open import Overture.Inverses                         using ( IsInjective ; id-is-injective ; ∘-injective )
open import Algebras.Setoid.Basic             {𝑆 = 𝑆} using ( SetoidAlgebra ; Lift-SetoidAlg )
open import Algebras.Products                 {𝑆 = 𝑆} using ( ov )
open import Homomorphisms.Setoid.Basic        {𝑆 = 𝑆} using ( hom ; ∘-hom )
open import Homomorphisms.Setoid.Isomorphisms {𝑆 = 𝑆} using ( _≅_ ; ≅toInjective ; ≅fromInjective
                                                            ;  ≅-sym ; ≅-refl ; ≅-trans ; Lift-≅ )
open import Subalgebras.Setoid.Subalgebras    {𝑆 = 𝑆} using ( _≤_ ; _≥_ ; _IsSubalgebraOfClass_ )

private variable α ρᵃ β ρᵇ γ ρᶜ : Level

\end{code}

The subalgebra relation is a *preorder*, i.e., a reflexive, transitive binary relation.

\begin{code}

open _≅_

≅→≤ : {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ} → 𝑨 ≅ 𝑩 → 𝑨 ≤ 𝑩
≅→≤ φ = (to φ) , ≅toInjective φ

≅→≥ : {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ} → 𝑨 ≅ 𝑩 → 𝑨 ≥ 𝑩
≅→≥ φ = (from φ) , ≅fromInjective φ

≤-refl : {𝑨 𝑩 : SetoidAlgebra α ρᵃ} → 𝑨 ≅ 𝑩 → 𝑨 ≤ 𝑩
≤-refl {𝑨 = 𝑨}{𝑩} A≅B = ≅→≤ A≅B

≥-refl : {𝑨 𝑩 : SetoidAlgebra α ρᵃ} → 𝑨 ≅ 𝑩 → 𝑨 ≥ 𝑩
≥-refl {𝑨 = 𝑨}{𝑩} A≅B = ≅→≤ (≅-sym A≅B)


≤-reflexive : {𝑨 : SetoidAlgebra α ρᵃ} → 𝑨 ≤ 𝑨
≤-reflexive {𝑨 = 𝑨} = (id , λ f a → refl) , Injection.injective id-is-injective


≤-trans : (𝑨 : SetoidAlgebra α ρᵃ){𝑩 : SetoidAlgebra β ρᵇ}(𝑪 : SetoidAlgebra γ ρᶜ)
  →        𝑨 ≤ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪

≤-trans 𝑨 {𝑩} 𝑪 A≤B B≤C = (∘-hom 𝑨 𝑩 𝑪 ∣ A≤B ∣ ∣ B≤C ∣ ) , ∘-injective ∥ A≤B ∥ ∥ B≤C ∥

≥-trans : (𝑨 : SetoidAlgebra α ρᵃ){𝑩 : SetoidAlgebra β ρᵇ}(𝑪 : SetoidAlgebra γ ρᶜ)
  →        𝑨 ≥ 𝑩 → 𝑩 ≥ 𝑪 → 𝑨 ≥ 𝑪
≥-trans 𝑨 {𝑩} 𝑪 A≥B B≥C = ≤-trans 𝑪 {𝑩} 𝑨 B≥C A≥B


module _ {α ρᵃ ρ : Level} where

 open import Relation.Binary.Structures {a = ov(α ⊔ ρᵃ)}{ℓ = (𝓞 ⊔ 𝓥 ⊔ α)} (_≅_ {α}{ρᵃ}{α}{ρᵃ})

 open IsPreorder
 ≤-preorder : IsPreorder _≤_
 isEquivalence ≤-preorder = record { refl = ≅-refl ; sym = ≅-sym ; trans = ≅-trans }
 reflexive ≤-preorder = ≤-refl
 trans ≤-preorder {𝑨}{𝑩}{𝑪} A≤B B≤C = ≤-trans 𝑨 {𝑩} 𝑪 A≤B B≤C



open _≅_

module _ {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ}{𝑪 : SetoidAlgebra γ ρᶜ} where

 A≥B×B≅C→A≥C : 𝑨 ≥ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≥ 𝑪
 A≥B×B≅C→A≥C A≥B B≅C  = ≥-trans 𝑨 {𝑩} 𝑪 A≥B (≅→≥ B≅C)

 A≤B×B≅C→A≤C : 𝑨 ≤ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≤ 𝑪
 A≤B×B≅C→A≤C A≤B B≅C = ≤-trans 𝑨{𝑩} 𝑪 A≤B (≅→≤ B≅C)

 A≅B×B≥C→A≥C : 𝑨 ≅ 𝑩 → 𝑩 ≥ 𝑪 → 𝑨 ≥ 𝑪

 A≅B×B≥C→A≥C A≅B B≥C = ≥-trans 𝑨{𝑩}𝑪 (≅→≥ A≅B) B≥C

 A≅B×B≤C→A≤C : 𝑨 ≅ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪
 A≅B×B≤C→A≤C A≅B B≤C = ≤-trans 𝑨{𝑩}𝑪 (≅→≤ A≅B) B≤C


≤-TRANS-≅ : (𝑨 : SetoidAlgebra α ρᵃ){𝑩 : SetoidAlgebra β ρᵇ}(𝑪 : SetoidAlgebra γ ρᶜ)
 →          𝑨 ≤ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≤ 𝑪
≤-TRANS-≅ 𝑨 {𝑩} 𝑪 (h , hinj) B≅C = (∘-hom 𝑨 𝑩 𝑪 h (to B≅C)) , ∘-injective hinj (≅toInjective B≅C)

≤-mono : (𝑩 : SetoidAlgebra β ρᵇ){𝒦 𝒦' : Pred (SetoidAlgebra α ρᵃ) γ}
 →        𝒦 ⊆ 𝒦' → 𝑩 IsSubalgebraOfClass 𝒦 → 𝑩 IsSubalgebraOfClass 𝒦'

≤-mono 𝑩 KK' (𝑨 , (KA , B≤A)) = 𝑨 , ((KK' KA) , B≤A)

\end{code}

#### <a id="lifts-of-subalgebras">Lifts of subalgebras</a>

\begin{code}

module _ {𝒦 : Pred (SetoidAlgebra α ρᵃ)(ov α)}{𝑩 : SetoidAlgebra β ρᵇ}{ℓ : Level} where

 Lift-is-sub : 𝑩 IsSubalgebraOfClass 𝒦 → (Lift-SetoidAlg 𝑩 ℓ) IsSubalgebraOfClass 𝒦
 Lift-is-sub (𝑨 , (KA , B≤A)) = 𝑨 , (KA , A≥B×B≅C→A≥C {𝑨 = 𝑨}{𝑩} B≤A Lift-≅)

≤-Lift : (𝑨 : SetoidAlgebra α ρᵃ){𝑩 : SetoidAlgebra β ρᵇ}{ℓ : Level} → 𝑨 ≤ 𝑩 → 𝑨 ≤ Lift-SetoidAlg 𝑩 ℓ
≤-Lift 𝑨 {𝑩}{ℓ} A≤B = A≤B×B≅C→A≤C{𝑨 = 𝑨}{𝑩}  A≤B Lift-≅

≥-Lift : (𝑨 : SetoidAlgebra α ρᵃ){𝑩 : SetoidAlgebra β ρᵇ}{ℓ : Level} → 𝑨 ≥ 𝑩 → 𝑨 ≥ Lift-SetoidAlg 𝑩 ℓ
≥-Lift 𝑨 {𝑩}{ℓ} A≥B = A≥B×B≅C→A≥C {𝑨 = 𝑨}{𝑩} A≥B Lift-≅

Lift-≤-Lift : {𝑨 : SetoidAlgebra α ρᵃ}(ℓᵃ : Level){𝑩 : SetoidAlgebra β ρᵇ}(ℓᵇ : Level)
 →             𝑨 ≤ 𝑩 → Lift-SetoidAlg 𝑨 ℓᵃ ≤ Lift-SetoidAlg 𝑩 ℓᵇ
Lift-≤-Lift {𝑨 = 𝑨} ℓᵃ {𝑩} ℓᵇ A≤B = ≥-Lift (Lift-SetoidAlg 𝑩 ℓᵇ){𝑨} (≤-Lift 𝑨{𝑩} A≤B)

\end{code}

---------------------------------

<br>

[← Subalgebras.Setoid.Subalgebras](Subalgebras.Setoid.Subalgebras.html)
<span style="float:right;">[Varieties →](Varieties.html)</span>

{% include UALib.Links.md %}

