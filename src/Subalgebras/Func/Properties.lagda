---
layout: default
title : "Subalgebras.Func.Properties module (The Agda Universal Algebra Library)"
date : "2021-07-18"
author: "agda-algebras development team"
---

#### <a id="properties-of-the-subalgebra-relation">Properties of the subalgebra relation for setoid algebras</a>

This is the [Subalgebras.Func.Properties][] module of the [Agda Universal Algebra Library][].


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Subalgebras.Func.Properties {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ------------------------------------
open import Agda.Primitive   using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type )
open import Data.Product     using ( _,_ ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Function.Base    using ( _∘_ )
open import Function.Bundles using ( Func )
open import Relation.Binary  using ( Setoid )
open import Relation.Unary   using ( Pred ; _⊆_ )
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ---------------------------------------------------
open import Overture.Preliminaries                  using ( ∣_∣ ; ∥_∥ )
open import Overture.Func.Preliminaries             using ( _⟶_ )
open import Overture.Func.Injective                 using ( id-is-injective ; module compose ; IsInjective )
open import Algebras.Func.Basic             {𝑆 = 𝑆} using ( SetoidAlgebra ; Lift-Algˡ ; Lift-Algʳ ; Lift-Alg ; ov )
open import Algebras.Func.Products          {𝑆 = 𝑆} using ( ⨅ )
open import Homomorphisms.Func.Basic        {𝑆 = 𝑆} using ( hom ; IsHom )
open import Homomorphisms.Func.Properties   {𝑆 = 𝑆} using ( 𝒾𝒹 ; ∘-hom )
open import Homomorphisms.Func.Isomorphisms {𝑆 = 𝑆} using ( _≅_ ; ≅toInjective ; ≅fromInjective ; mkiso
                                                          ; ≅-sym ; ≅-refl ; ≅-trans ; Lift-≅ˡ ; Lift-≅ ; Lift-≅ʳ)
open import Subalgebras.Func.Subalgebras  {𝑆 = 𝑆} using ( _≤_ ; _≥_ ; _IsSubalgebraOfClass_ ; _≤c_ )

private variable
 α ρᵃ β ρᵇ γ ρᶜ ι : Level

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

module _ {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ}{𝑪 : SetoidAlgebra γ ρᶜ} where
 open SetoidAlgebra using ( Domain )
 open Setoid (Domain 𝑨) using () renaming ( _≈_ to _≈₁_ ; Carrier to ∣A∣ )
 open Setoid (Domain 𝑩) using () renaming ( _≈_ to _≈₂_ ; Carrier to ∣B∣ )
 open Setoid (Domain 𝑪) using () renaming ( _≈_ to _≈₃_ ; Carrier to ∣C∣ )
 open compose {A = ∣A∣}{B = ∣B∣}{C = ∣C∣} _≈₁_ _≈₂_ _≈₃_ using ( ∘-injective-func )

 ≤-trans : 𝑨 ≤ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪
 ≤-trans A≤B B≤C = (∘-hom ∣ A≤B ∣ ∣ B≤C ∣ ) , ∘-injective-func ∥ A≤B ∥ ∥ B≤C ∥

 ≤-trans-≅ : 𝑨 ≤ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≤ 𝑪
 ≤-trans-≅ (h , hinj) B≅C = (∘-hom h (to B≅C)) , ∘-injective-func hinj (≅toInjective B≅C)

 ≅-trans-≤ : 𝑨 ≅ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪
 ≅-trans-≤ A≅B (h , hinj) = (∘-hom (to A≅B) h) , (∘-injective-func (≅toInjective A≅B) hinj)

module _ {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ}{𝑪 : SetoidAlgebra γ ρᶜ} where
 ≥-trans : 𝑨 ≥ 𝑩 → 𝑩 ≥ 𝑪 → 𝑨 ≥ 𝑪
 ≥-trans A≥B B≥C = ≤-trans B≥C A≥B

≤→≤c→≤c : {𝑨 : SetoidAlgebra α α}{𝑩 : SetoidAlgebra α α}{𝒦 : Pred(SetoidAlgebra α α) (ov α)}
 →        𝑨 ≤ 𝑩 → 𝑩 ≤c 𝒦 → 𝑨 ≤c 𝒦
≤→≤c→≤c {𝑨 = 𝑨} A≤B sB = ∣ sB ∣ , (fst ∥ sB ∥ , ≤-trans A≤B (snd ∥ sB ∥))


module _ {α ρᵃ ρ : Level} where

 open import Relation.Binary.Structures {a = ov(α ⊔ ρᵃ)}{ℓ = (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ)} (_≅_ {α}{ρᵃ}{α}{ρᵃ})

 open IsPreorder
 ≤-preorder : IsPreorder _≤_
 isEquivalence ≤-preorder = record { refl = ≅-refl ; sym = ≅-sym ; trans = ≅-trans }
 reflexive ≤-preorder = ≤-refl
 trans ≤-preorder {𝑨}{𝑩}{𝑪} A≤B B≤C = ≤-trans A≤B B≤C



open _≅_

module _ {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ}{𝑪 : SetoidAlgebra γ ρᶜ} where

 A≥B×B≅C→A≥C : 𝑨 ≥ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≥ 𝑪
 A≥B×B≅C→A≥C A≥B B≅C  = ≥-trans A≥B (≅→≥ B≅C)

 A≤B×B≅C→A≤C : 𝑨 ≤ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≤ 𝑪
 A≤B×B≅C→A≤C A≤B B≅C = ≤-trans  A≤B (≅→≤ B≅C)

 A≅B×B≥C→A≥C : 𝑨 ≅ 𝑩 → 𝑩 ≥ 𝑪 → 𝑨 ≥ 𝑪

 A≅B×B≥C→A≥C A≅B B≥C = ≥-trans (≅→≥ A≅B) B≥C

 A≅B×B≤C→A≤C : 𝑨 ≅ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪
 A≅B×B≤C→A≤C A≅B B≤C = ≤-trans (≅→≤ A≅B) B≤C

open Func using ( cong ) renaming ( f to _⟨$⟩_ )
module _ {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ} where
 open SetoidAlgebra 𝑨 using () renaming (Domain to A)
 open SetoidAlgebra 𝑩 using () renaming (Domain to B)
 open Setoid A using ( sym )
-- open ≡-Reasoning
 open SetoidReasoning A

 iso→injective : (φ : 𝑨 ≅ 𝑩) → IsInjective ∣ to φ ∣
 iso→injective (mkiso f g f∼g g∼f) {x}{y} fxfy =
  begin
   x                        ≈˘⟨ g∼f x ⟩
   ∣ g ∣ ⟨$⟩ (∣ f ∣ ⟨$⟩ x)  ≈⟨ cong ∣ g ∣ fxfy ⟩
   ∣ g ∣ ⟨$⟩ (∣ f ∣ ⟨$⟩ y)  ≈⟨ g∼f y ⟩
   y
  ∎

≤-mono : (𝑩 : SetoidAlgebra β ρᵇ){𝒦 𝒦' : Pred (SetoidAlgebra α ρᵃ) γ}
 →        𝒦 ⊆ 𝒦' → 𝑩 ≤c 𝒦 → 𝑩 ≤c 𝒦'
≤-mono 𝑩 KK' (𝑨 , (KA , B≤A)) = 𝑨 , ((KK' KA) , B≤A)

\end{code}


#### <a id="lifts-of-subalgebras-of-setoid-algebras">Lifts of subalgebras of setoid algebras</a>

\begin{code}

module _ {𝒦 : Pred (SetoidAlgebra α ρᵃ)(ov α)}{𝑩 : SetoidAlgebra β ρᵇ}{ℓ : Level} where

 Lift-is-sub : 𝑩 ≤c 𝒦 → (Lift-Algˡ 𝑩 ℓ) ≤c 𝒦
 Lift-is-sub (𝑨 , (KA , B≤A)) = 𝑨 , (KA , A≥B×B≅C→A≥C {𝑨 = 𝑨}{𝑩} B≤A Lift-≅ˡ)

module _ {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ} where

 ≤-Liftˡ : {ℓ : Level} → 𝑨 ≤ 𝑩 → 𝑨 ≤ Lift-Algˡ 𝑩 ℓ
 ≤-Liftˡ A≤B = A≤B×B≅C→A≤C A≤B Lift-≅ˡ

 ≤-Liftʳ : {ρ : Level} → 𝑨 ≤ 𝑩 → 𝑨 ≤ Lift-Algʳ 𝑩 ρ
 ≤-Liftʳ A≤B = A≤B×B≅C→A≤C A≤B Lift-≅ʳ

 ≤-Lift : {ℓ ρ : Level} → 𝑨 ≤ 𝑩 → 𝑨 ≤ Lift-Alg 𝑩 ℓ ρ
 ≤-Lift A≤B = A≤B×B≅C→A≤C  A≤B Lift-≅

 ≥-Liftˡ : {ℓ : Level} → 𝑨 ≥ 𝑩 → 𝑨 ≥ Lift-Algˡ 𝑩 ℓ
 ≥-Liftˡ A≥B = A≥B×B≅C→A≥C A≥B Lift-≅ˡ

 ≥-Liftʳ : {ρ : Level} → 𝑨 ≥ 𝑩 → 𝑨 ≥ Lift-Algʳ 𝑩 ρ
 ≥-Liftʳ A≥B = A≥B×B≅C→A≥C A≥B Lift-≅ʳ

 ≥-Lift : {ℓ ρ : Level} → 𝑨 ≥ 𝑩 → 𝑨 ≥ Lift-Alg 𝑩 ℓ ρ
 ≥-Lift A≥B = A≥B×B≅C→A≥C A≥B Lift-≅

module _ {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ} where

 Lift-≤-Liftˡ : {ℓᵃ ℓᵇ : Level} → 𝑨 ≤ 𝑩 → Lift-Algˡ 𝑨 ℓᵃ ≤ Lift-Algˡ 𝑩 ℓᵇ
 Lift-≤-Liftˡ A≤B = ≥-Liftˡ (≤-Liftˡ A≤B)

 Lift-≤-Liftʳ : {rᵃ rᵇ : Level} → 𝑨 ≤ 𝑩 → Lift-Algʳ 𝑨 rᵃ ≤ Lift-Algʳ 𝑩 rᵇ
 Lift-≤-Liftʳ A≤B = ≥-Liftʳ (≤-Liftʳ A≤B)

 Lift-≤-Lift : {a rᵃ b rᵇ : Level}
  →             𝑨 ≤ 𝑩 → Lift-Alg 𝑨 a rᵃ ≤ Lift-Alg 𝑩 b rᵇ
 Lift-≤-Lift A≤B = ≥-Lift (≤-Lift A≤B)

\end{code}


#### Products of subalgebras

\begin{code}

module _ {I : Type ι}{𝒜 : I → SetoidAlgebra α ρᵃ}{ℬ : I → SetoidAlgebra β ρᵇ} where

 open SetoidAlgebra (⨅ 𝒜) using () renaming ( Domain to ⨅A )
 open SetoidAlgebra (⨅ ℬ) using () renaming ( Domain to ⨅B )
 open Setoid ⨅A using ( refl )
 open IsHom
 ⨅-≤ : (∀ i → ℬ i ≤ 𝒜 i) → ⨅ ℬ ≤ ⨅ 𝒜
 ⨅-≤ B≤A = h , hM
  where
  h : hom (⨅ ℬ) (⨅ 𝒜)
  h = hfunc , hhom
   where
   hi : ∀ i → hom (ℬ i) (𝒜 i)
   hi i = ∣ B≤A i ∣

   hfunc : ⨅B ⟶ ⨅A
   (hfunc ⟨$⟩ x) i = ∣ hi i ∣ ⟨$⟩ (x i)
   cong hfunc = λ xy i → cong ∣ hi i ∣ (xy i)
   hhom : IsHom (⨅ ℬ) (⨅ 𝒜) hfunc
   compatible hhom = λ i → compatible ∥ hi i ∥

  hM : IsInjective ∣ h ∣
  hM = λ xy i → ∥ B≤A i ∥ (xy i)

\end{code}


---------------------------------

<span style="float:left;">[← Subalgebras.Func.Subalgebras](Subalgebras.Func.Subalgebras.html)</span>
<span style="float:right;">[Varieties →](Varieties.html)</span>

{% include UALib.Links.md %}