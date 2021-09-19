---
layout: default
title : "Subalgebras.Setoid.Properties module (The Agda Universal Algebra Library)"
date : "2021-07-18"
author: "agda-algebras development team"
---

#### <a id="properties-of-the-subalgebra-relation">Properties of the subalgebra relation for setoid algebras</a>

This is the [Subalgebras.Setoid.Properties][] module of the [Agda Universal Algebra Library][].


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Subalgebras.Setoid.Properties {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ------------------------------------
open import Agda.Primitive   using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type )
open import Data.Product     using ( _,_ )
open import Relation.Binary  using ( Setoid )
open import Relation.Unary   using ( Pred ; _⊆_ )

-- Imports from the Agda Universal Algebra Library ---------------------------------------------------
open import Overture.Preliminaries                  using ( ∣_∣ ; ∥_∥ )
open import Overture.Func.Injective                 using ( id-is-injective ; module compose )
open import Algebras.Setoid.Basic           {𝑆 = 𝑆} using ( SetoidAlgebra ; Lift-Alg )
open import Algebras.Products               {𝑆 = 𝑆} using ( ov )
open import Homomorphisms.Func.Properties   {𝑆 = 𝑆} using ( 𝒾𝒹 ; ∘-hom )
open import Homomorphisms.Func.Isomorphisms {𝑆 = 𝑆} using ( _≅_ ; ≅toInjective ; ≅fromInjective
                                                          ; ≅-sym ; ≅-refl ; ≅-trans ; Lift-≅ )
open import Subalgebras.Setoid.Subalgebras  {𝑆 = 𝑆} using ( _≤_ ; _≥_ ; _IsSubalgebraOfClass_ )

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
≤-reflexive {𝑨 = 𝑨} = 𝒾𝒹 , id-is-injective{𝑨 = SetoidAlgebra.Domain 𝑨}

module _ (𝑨 : SetoidAlgebra α ρᵃ){𝑩 : SetoidAlgebra β ρᵇ}(𝑪 : SetoidAlgebra γ ρᶜ) where
 open SetoidAlgebra using ( Domain )
 open Setoid (Domain 𝑨) using () renaming ( _≈_ to _≈₁_ ; Carrier to ∣A∣ )
 open Setoid (Domain 𝑩) using () renaming ( _≈_ to _≈₂_ ; Carrier to ∣B∣ )
 open Setoid (Domain 𝑪) using () renaming ( _≈_ to _≈₃_ ; Carrier to ∣C∣ )
 open compose {A = ∣A∣}{B = ∣B∣}{C = ∣C∣} _≈₁_ _≈₂_ _≈₃_ using ( ∘-injective-func )

 ≤-trans : 𝑨 ≤ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪
 ≤-trans A≤B B≤C = (∘-hom ∣ A≤B ∣ ∣ B≤C ∣ ) , ∘-injective-func ∥ A≤B ∥ ∥ B≤C ∥

 ≤-TRANS-≅ : 𝑨 ≤ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≤ 𝑪
 ≤-TRANS-≅ (h , hinj) B≅C = (∘-hom h (to B≅C)) , ∘-injective-func hinj (≅toInjective B≅C)

≥-trans : (𝑨 : SetoidAlgebra α ρᵃ){𝑩 : SetoidAlgebra β ρᵇ}(𝑪 : SetoidAlgebra γ ρᶜ)
 →        𝑨 ≥ 𝑩 → 𝑩 ≥ 𝑪 → 𝑨 ≥ 𝑪
≥-trans 𝑨 {𝑩} 𝑪 A≥B B≥C = ≤-trans 𝑪 {𝑩} 𝑨 B≥C A≥B



module _ {α ρᵃ ρ : Level} where

 open import Relation.Binary.Structures {a = ov(α ⊔ ρᵃ)}{ℓ = (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ)} (_≅_ {α}{ρᵃ}{α}{ρᵃ})

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



≤-mono : (𝑩 : SetoidAlgebra β ρᵇ){𝒦 𝒦' : Pred (SetoidAlgebra α ρᵃ) γ}
 →        𝒦 ⊆ 𝒦' → 𝑩 IsSubalgebraOfClass 𝒦 → 𝑩 IsSubalgebraOfClass 𝒦'

≤-mono 𝑩 KK' (𝑨 , (KA , B≤A)) = 𝑨 , ((KK' KA) , B≤A)

\end{code}



#### <a id="lifts-of-subalgebras-of-setoid-algebras">Lifts of subalgebras of setoid algebras</a>

\begin{code}

module _ {𝒦 : Pred (SetoidAlgebra α ρᵃ)(ov α)}{𝑩 : SetoidAlgebra β ρᵇ}{ℓ : Level} where

 Lift-is-sub : 𝑩 IsSubalgebraOfClass 𝒦 → (Lift-Alg 𝑩 ℓ) IsSubalgebraOfClass 𝒦
 Lift-is-sub (𝑨 , (KA , B≤A)) = 𝑨 , (KA , A≥B×B≅C→A≥C {𝑨 = 𝑨}{𝑩} B≤A Lift-≅)

≤-Lift : (𝑨 : SetoidAlgebra α ρᵃ){𝑩 : SetoidAlgebra β ρᵇ}{ℓ : Level} → 𝑨 ≤ 𝑩 → 𝑨 ≤ Lift-Alg 𝑩 ℓ
≤-Lift 𝑨 {𝑩}{ℓ} A≤B = A≤B×B≅C→A≤C{𝑨 = 𝑨}{𝑩}  A≤B Lift-≅

≥-Lift : (𝑨 : SetoidAlgebra α ρᵃ){𝑩 : SetoidAlgebra β ρᵇ}{ℓ : Level} → 𝑨 ≥ 𝑩 → 𝑨 ≥ Lift-Alg 𝑩 ℓ
≥-Lift 𝑨 {𝑩}{ℓ} A≥B = A≥B×B≅C→A≥C {𝑨 = 𝑨}{𝑩} A≥B Lift-≅

Lift-≤-Lift : {𝑨 : SetoidAlgebra α ρᵃ}(ℓᵃ : Level){𝑩 : SetoidAlgebra β ρᵇ}(ℓᵇ : Level)
 →             𝑨 ≤ 𝑩 → Lift-Alg 𝑨 ℓᵃ ≤ Lift-Alg 𝑩 ℓᵇ
Lift-≤-Lift {𝑨 = 𝑨} ℓᵃ {𝑩} ℓᵇ A≤B = ≥-Lift (Lift-Alg 𝑩 ℓᵇ){𝑨} (≤-Lift 𝑨{𝑩} A≤B)

\end{code}

---------------------------------

<span style="float:left;">[← Subalgebras.Setoid.Subalgebras](Subalgebras.Setoid.Subalgebras.html)</span>
<span style="float:right;">[Varieties →](Varieties.html)</span>

{% include UALib.Links.md %}
