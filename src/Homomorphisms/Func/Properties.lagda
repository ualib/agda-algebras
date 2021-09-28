---
layout: default
title : "Homomorphisms.Func.Properties module (Agda Universal Algebra Library)"
date : "2021-09-13"
author: "agda-algebras development team"
---

#### <a id="properties-of-homomorphisms-of-setoidalgebras">Properties of Homomorphisms of SetoidAlgebras</a>

This is the [Homomorphisms.Func.Properties][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using (𝓞 ; 𝓥 ; Signature )

module Homomorphisms.Func.Properties {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ------------------------------------------
open import Data.Product    using ( _,_ ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Function        using ( id )
open import Function.Bundles  using ( Func )
open import Level           using ( Level )
open import Relation.Binary using (  Setoid )
open import Relation.Binary.PropositionalEquality as ≡ using ( _≡_ )

-- Imports from the Agda Universal Algebra Library ------------------------------------------
open import Overture.Preliminaries           using ( ∣_∣ )
open import Overture.Func.Preliminaries      using ( _⟶_ ; _∘_ ; 𝑖𝑑 )
open import Algebras.Func.Basic      {𝑆 = 𝑆} using ( SetoidAlgebra ; _̂_ ; Lift-Algˡ ; Lift-Algʳ ; Lift-Alg ; 𝕌[_] )
open import Homomorphisms.Func.Basic {𝑆 = 𝑆} using ( IsHom ; compatible-map ; ≈preserving ; hom )
open Func using ( cong ) renaming (f to _⟨$⟩_ )

private variable
 α β γ ρᵃ ρᵇ ρᶜ ℓ : Level

\end{code}

##### <a id="lifting-and-lowering">Lifting and lowering of homs</a>

First we define the identity homomorphism for setoid algebras and then we prove that the operations of lifting and lowering of a setoid algebra are homomorphisms.

\begin{code}

module _ {𝑨 : SetoidAlgebra α ρᵃ} where
 open SetoidAlgebra 𝑨 using () renaming (Domain to A )
 open Setoid A using ( reflexive ) renaming ( _≈_ to _≈₁_ ; refl to refl₁ )

 𝒾𝒹 :  hom 𝑨 𝑨
 𝒾𝒹 = 𝑖𝑑 , record { compatible = reflexive ≡.refl
                 ; preserves≈ = id }



module _ {𝑨 : SetoidAlgebra α ρᵃ}{ℓ : Level} where
 open SetoidAlgebra 𝑨 using () renaming (Domain to A )
 open Setoid A using ( reflexive ) renaming ( _≈_ to _≈₁_ ; refl to refl₁ )

 open SetoidAlgebra  using ( Domain )
 open Setoid (Domain (Lift-Algˡ 𝑨 ℓ)) using () renaming ( _≈_ to _≈ˡ_ ; refl to reflˡ)
 open Setoid (Domain (Lift-Algʳ 𝑨 ℓ)) using () renaming ( _≈_ to _≈ʳ_ ; refl to reflʳ)

 open Level
 ToLiftˡ : hom 𝑨 (Lift-Algˡ 𝑨 ℓ)
 ToLiftˡ = record { f = lift ; cong = id }
         , record { compatible = reflexive ≡.refl
                  ; preserves≈ = id }

 FromLiftˡ : hom (Lift-Algˡ 𝑨 ℓ) 𝑨
 FromLiftˡ = record { f = lower ; cong = id }
                   , record { compatible = reflˡ
                            ; preserves≈ = id }

 ToFromLiftˡ : ∀ b →  (∣ ToLiftˡ ∣ ⟨$⟩ (∣ FromLiftˡ ∣ ⟨$⟩ b)) ≈ˡ b
 ToFromLiftˡ b = refl₁

 FromToLiftˡ : ∀ a → (∣ FromLiftˡ ∣ ⟨$⟩ (∣ ToLiftˡ ∣ ⟨$⟩ a)) ≈₁ a
 FromToLiftˡ a = refl₁


 ToLiftʳ : hom 𝑨 (Lift-Algʳ 𝑨 ℓ)
 ToLiftʳ = record { f = id ; cong = lift }
         , record { compatible = lift (reflexive ≡.refl)
                  ; preserves≈ = lift }

 FromLiftʳ : hom (Lift-Algʳ 𝑨 ℓ) 𝑨
 FromLiftʳ = record { f = id ; cong = lower }
           , record { compatible = reflˡ
                    ; preserves≈ = lower }

 ToFromLiftʳ : ∀ b → (∣ ToLiftʳ ∣ ⟨$⟩ (∣ FromLiftʳ ∣ ⟨$⟩ b)) ≈ʳ b
 ToFromLiftʳ b = lift refl₁

 FromToLiftʳ : ∀ a → (∣ FromLiftʳ ∣ ⟨$⟩ (∣ ToLiftʳ ∣ ⟨$⟩ a)) ≈₁ a
 FromToLiftʳ a = refl₁

\end{code}


##### <a id="composition-of-homs">Composition of homs</a>

\begin{code}

module _ {𝑨 : SetoidAlgebra α ρᵃ}
         {𝑩 : SetoidAlgebra β ρᵇ}
         {𝑪 : SetoidAlgebra γ ρᶜ} where

  open SetoidAlgebra 𝑨 using () renaming (Domain to A )
  open SetoidAlgebra 𝑩 using () renaming (Domain to B )
  open SetoidAlgebra 𝑪 using () renaming (Domain to C )
  open Setoid A using ()        renaming ( _≈_ to _≈₁_ )
  open Setoid B using ()        renaming ( _≈_ to _≈₂_ )
  open Setoid C using ( trans ) renaming ( _≈_ to _≈₃_ )

  open IsHom

  -- The composition of homomorphisms is again a homomorphism
  ∘-is-hom : {g : A ⟶ B}{h : B ⟶ C}
   →         IsHom 𝑨 𝑩 g → IsHom 𝑩 𝑪 h
   →         IsHom 𝑨 𝑪 (h ∘ g)

  ∘-is-hom {g} {h} ghom hhom = record { compatible = i ; preserves≈ = ii }
   where
   i : compatible-map 𝑨 𝑪 (h ∘ g)
   i {f}{a} = trans lemg lemh
    where
    lemg : (h ⟨$⟩ (g ⟨$⟩ ((f ̂ 𝑨) a))) ≈₃ (h ⟨$⟩ ((f ̂ 𝑩) (λ x → g ⟨$⟩ (a x))))
    lemg = preserves≈ hhom (compatible ghom)

    lemh : (h ⟨$⟩ ((f ̂ 𝑩) (λ x → g ⟨$⟩ (a x)))) ≈₃ ((f ̂ 𝑪) (λ x → h ⟨$⟩ (g ⟨$⟩ (a x))))
    lemh = compatible hhom
   ii : ≈preserving 𝑨 𝑪 (h ∘ g)
   ii xy = preserves≈ hhom (preserves≈ ghom xy)

  ∘-hom : hom 𝑨 𝑩 → hom 𝑩 𝑪  → hom 𝑨 𝑪
  ∘-hom (h , hhom) (g , ghom) = (g ∘ h) , ∘-is-hom hhom ghom

\end{code}

Next we formalize the fact that a homomorphism from `𝑨` to `𝑩` can be lifted to a homomorphism from `Lift-Alg 𝑨 ℓᵃ` to `Lift-Alg 𝑩 ℓᵇ`.

\begin{code}

module _ {𝑨 : SetoidAlgebra α ρᵃ} {𝑩 : SetoidAlgebra β ρᵇ} where

 open SetoidAlgebra     using ( Domain )
 open Setoid            using ( _≈_ )
 open Setoid (Domain 𝑨) using ( reflexive ) renaming ( _≈_ to _≈₁_ )
 open Setoid (Domain 𝑩) using ()            renaming ( _≈_ to _≈₂_ )
 open Level

 Lift-hom : hom 𝑨 𝑩  → (ℓᵃ ℓᵇ : Level) →  hom (Lift-Algˡ 𝑨 ℓᵃ) (Lift-Algˡ 𝑩 ℓᵇ)
 Lift-hom (f , fhom) ℓᵃ ℓᵇ = ϕ , Goal
  where
  lA lB : SetoidAlgebra _ _
  lA = Lift-Algˡ 𝑨 ℓᵃ
  lB = Lift-Algˡ 𝑩 ℓᵇ

  ψ : Domain lA ⟶ Domain 𝑩
  ψ = record { f = λ x → f ⟨$⟩ (lower x) ; cong = cong f }

  lABh : IsHom lA 𝑩 ψ
  lABh = ∘-is-hom {𝑨 = lA}{𝑩 = 𝑨}{𝑩} (snd FromLiftˡ) fhom

  ϕ : Domain lA ⟶ Domain lB
  ϕ = record { f = λ x → lift ((f ⟨$⟩ (lower x))) ; cong = cong f }

  Goal : IsHom lA lB ϕ
  Goal = ∘-is-hom {𝑨 = lA}{𝑩 = 𝑩}{lB} lABh (snd ToLiftˡ)

 lift-hom-lemma : (h : hom 𝑨 𝑩)(a : 𝕌[ 𝑨 ])(ℓᵃ ℓᵇ : Level)
  →               (_≈_ (Domain (Lift-Algˡ 𝑩 ℓᵇ))) (lift (∣ h ∣ ⟨$⟩ a))
                  (∣ Lift-hom h ℓᵃ ℓᵇ ∣ ⟨$⟩ lift a)
 lift-hom-lemma h a ℓᵃ ℓᵇ = Setoid.refl (Domain 𝑩)

\end{code}

--------------------------------

<span style="float:left;">[← Homomorphisms.Func.Basic](Homomorphisms.Func.Basic.html)</span>
<span style="float:right;">[Homomorphisms.Func.Kernels →](Homomorphisms.Func.Kernels.html)</span>

{% include UALib.Links.md %}
