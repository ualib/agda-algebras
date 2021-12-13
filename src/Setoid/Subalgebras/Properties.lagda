---
layout: default
title : "Setoid.Subalgebras.Properties module (The Agda Universal Algebra Library)"
date : "2021-07-18"
author: "agda-algebras development team"
---

#### <a id="properties-of-the-subalgebra-relation">Properties of the subalgebra relation for setoid algebras</a>

This is the [Setoid.Subalgebras.Properties][] module of the [Agda Universal Algebra Library][].


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Base.Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Subalgebras.Properties {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ------------------------------------
open import Agda.Primitive   using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type )
open import Data.Product     using ( _,_ ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Function         using ( _∘_ ) renaming ( Func to _⟶_ )
open import Relation.Binary  using ( Setoid )
open import Relation.Unary   using ( Pred ; _⊆_ )
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ---------------------------------------------------
open import Base.Overture.Preliminaries                 using ( ∣_∣ ; ∥_∥ )
open import Setoid.Overture.Injective              using ( id-is-injective ; module compose )
                                                        using ( IsInjective ; ∘-injective )
open import Setoid.Algebras.Basic              {𝑆 = 𝑆}  using ( Algebra ; Lift-Algˡ )
                                                        using ( Lift-Algʳ ; Lift-Alg ; ov )
open import Setoid.Algebras.Products           {𝑆 = 𝑆}  using ( ⨅ )
open import Setoid.Homomorphisms.Basic         {𝑆 = 𝑆}  using ( hom ; IsHom )
open import Setoid.Homomorphisms.Properties    {𝑆 = 𝑆}  using ( 𝒾𝒹 ; ∘-hom )
open import Setoid.Homomorphisms.Isomorphisms  {𝑆 = 𝑆}  using ( _≅_ ; ≅toInjective ; ≅fromInjective )
                                                        using ( mkiso ; ≅-sym ; ≅-refl ; ≅-trans )
                                                        using ( Lift-≅ˡ ; Lift-≅ ; Lift-≅ʳ)
open import Setoid.Subalgebras.Subalgebras     {𝑆 = 𝑆}  using ( _≤_ ; _≥_ ; _IsSubalgebraOfClass_ ; _≤c_ )

private variable
 α ρᵃ β ρᵇ γ ρᶜ ι : Level

\end{code}

The subalgebra relation is a *preorder*, i.e., a reflexive, transitive binary relation.

\begin{code}

open _≅_

≅→≤ : {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} → 𝑨 ≅ 𝑩 → 𝑨 ≤ 𝑩
≅→≤ φ = (to φ) , ≅toInjective φ

≅→≥ : {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} → 𝑨 ≅ 𝑩 → 𝑨 ≥ 𝑩
≅→≥ φ = (from φ) , ≅fromInjective φ

≤-refl : {𝑨 𝑩 : Algebra α ρᵃ} → 𝑨 ≅ 𝑩 → 𝑨 ≤ 𝑩
≤-refl {𝑨 = 𝑨}{𝑩} A≅B = ≅→≤ A≅B

≥-refl : {𝑨 𝑩 : Algebra α ρᵃ} → 𝑨 ≅ 𝑩 → 𝑨 ≥ 𝑩
≥-refl {𝑨 = 𝑨}{𝑩} A≅B = ≅→≤ (≅-sym A≅B)

≤-reflexive : {𝑨 : Algebra α ρᵃ} → 𝑨 ≤ 𝑨
≤-reflexive {𝑨 = 𝑨} = 𝒾𝒹 , id-is-injective{𝑨 = Algebra.Domain 𝑨}

module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}{𝑪 : Algebra γ ρᶜ} where
 open Algebra using ( Domain )
 open Setoid (Domain 𝑨) using () renaming ( _≈_ to _≈₁_ ; Carrier to ∣A∣ )
 open Setoid (Domain 𝑩) using () renaming ( _≈_ to _≈₂_ ; Carrier to ∣B∣ )
 open Setoid (Domain 𝑪) using () renaming ( _≈_ to _≈₃_ ; Carrier to ∣C∣ )


 ≤-trans : 𝑨 ≤ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪
 ≤-trans ( f , finj ) ( g , ginj ) = (∘-hom f g) , ∘-injective ∣ f ∣ ∣ g ∣ finj ginj

 ≤-trans-≅ : 𝑨 ≤ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≤ 𝑪
 ≤-trans-≅ (h , hinj) B≅C = (∘-hom h (to B≅C)) , ∘-injective ∣ h ∣ ∣ to B≅C ∣ hinj (≅toInjective B≅C)

 ≅-trans-≤ : 𝑨 ≅ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪
 ≅-trans-≤ A≅B (h , hinj) = (∘-hom (to A≅B) h) , (∘-injective ∣ to A≅B ∣ ∣ h ∣ (≅toInjective A≅B) hinj)

module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}{𝑪 : Algebra γ ρᶜ} where
 ≥-trans : 𝑨 ≥ 𝑩 → 𝑩 ≥ 𝑪 → 𝑨 ≥ 𝑪
 ≥-trans A≥B B≥C = ≤-trans B≥C A≥B

≤→≤c→≤c : {𝑨 : Algebra α α}{𝑩 : Algebra α α}{𝒦 : Pred(Algebra α α) (ov α)}
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

module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}{𝑪 : Algebra γ ρᶜ} where

 A≥B×B≅C→A≥C : 𝑨 ≥ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≥ 𝑪
 A≥B×B≅C→A≥C A≥B B≅C  = ≥-trans A≥B (≅→≥ B≅C)

 A≤B×B≅C→A≤C : 𝑨 ≤ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≤ 𝑪
 A≤B×B≅C→A≤C A≤B B≅C = ≤-trans  A≤B (≅→≤ B≅C)

 A≅B×B≥C→A≥C : 𝑨 ≅ 𝑩 → 𝑩 ≥ 𝑪 → 𝑨 ≥ 𝑪

 A≅B×B≥C→A≥C A≅B B≥C = ≥-trans (≅→≥ A≅B) B≥C

 A≅B×B≤C→A≤C : 𝑨 ≅ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪
 A≅B×B≤C→A≤C A≅B B≤C = ≤-trans (≅→≤ A≅B) B≤C

open _⟶_ using ( cong ) renaming ( f to _⟨$⟩_ )
module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} where
 open Algebra 𝑨 using () renaming (Domain to A)
 open Algebra 𝑩 using () renaming (Domain to B)
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

≤-mono : (𝑩 : Algebra β ρᵇ){𝒦 𝒦' : Pred (Algebra α ρᵃ) γ}
 →        𝒦 ⊆ 𝒦' → 𝑩 ≤c 𝒦 → 𝑩 ≤c 𝒦'
≤-mono 𝑩 KK' (𝑨 , (KA , B≤A)) = 𝑨 , ((KK' KA) , B≤A)

\end{code}


#### <a id="lifts-of-subalgebras-of-setoid-algebras">Lifts of subalgebras of setoid algebras</a>

\begin{code}

module _ {𝒦 : Pred (Algebra α ρᵃ)(ov α)}{𝑩 : Algebra β ρᵇ}{ℓ : Level} where

 Lift-is-sub : 𝑩 ≤c 𝒦 → (Lift-Algˡ 𝑩 ℓ) ≤c 𝒦
 Lift-is-sub (𝑨 , (KA , B≤A)) = 𝑨 , (KA , A≥B×B≅C→A≥C {𝑨 = 𝑨}{𝑩} B≤A Lift-≅ˡ)

module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} where

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

module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} where

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

module _ {I : Type ι}{𝒜 : I → Algebra α ρᵃ}{ℬ : I → Algebra β ρᵇ} where

 open Algebra (⨅ 𝒜) using () renaming ( Domain to ⨅A )
 open Algebra (⨅ ℬ) using () renaming ( Domain to ⨅B )
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

<span style="float:left;">[← Setoid.Subalgebras.Subalgebras](Setoid.Subalgebras.Subalgebras.html)</span>
<span style="float:right;">[Setoid.Varieties →](Setoid.Varieties.html)</span>

{% include UALib.Links.md %}
