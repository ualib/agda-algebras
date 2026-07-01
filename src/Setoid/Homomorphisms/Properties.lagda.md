---
layout: default
title : Setoid."Homomorphisms.Properties module (Agda Universal Algebra Library)"
date : "2021-09-13"
author: "agda-algebras development team"
---

#### Properties of Homomorphisms of Algebras

This is the [Setoid.Homomorphisms.Properties][] module of the [Agda Universal Algebra Library][].

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Homomorphisms.Properties {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ------------------------------------------
open import Data.Product                            using ( _,_ ; proj₁ ; proj₂ )
open import Function      renaming ( Func to _⟶_ )  using ( id ; _$_ ; _∘_ )
open import Level                                   using ( Level ; _⊔_ )
open import Relation.Binary                         using ( Setoid )
open import Relation.Binary.PropositionalEquality   using ( _≡_ ; refl)

-- Imports from the Agda Universal Algebra Library ------------------------------------------
open import Setoid.Algebras {𝑆 = 𝑆}             using  ( Algebra ; _^_ ; Lift-Algˡ ; 𝕌[_]
                                                       ; Lift-Algʳ ; Lift-Alg ; 𝔻[_] )
open import Setoid.Homomorphisms.Basic {𝑆 = 𝑆}  using  ( hom ; IsHom ; epi ; IsEpi
                                                       ; compatible-map )
open import Setoid.Functions                    using ( _⊙_ ; 𝑖𝑑 ; eq ; ⊙-IsSurjective )

open IsHom using ( compatible )

open _⟶_ using ( cong ) renaming ( to to _⟨$⟩_ )

private variable α β γ ρᵃ ρᵇ ρᶜ ℓ : Level
```


##### Composition of homs


```agda
module _  {𝑨 : Algebra α ρᵃ} {𝑩 : Algebra β ρᵇ} {𝑪 : Algebra γ ρᶜ} where
  open Algebra 𝑨  renaming (Domain to A )   using ()
  open Algebra 𝑩  renaming (Domain to B )   using ()
  open Algebra 𝑪  renaming (Domain to C )   using ()
  open Setoid A   renaming ( _≈_ to _≈₁_ )  using ()
  open Setoid C   renaming ( _≈_ to _≈₃_ )  using ( trans )

  -- The composition of homomorphisms is again a homomorphism
  ⊙-is-hom : {g : A ⟶ B} {h : B ⟶ C} → IsHom 𝑨 𝑩 g → IsHom 𝑩 𝑪 h → IsHom 𝑨 𝑪 (h ⊙ g)
  ⊙-is-hom {g} {h} ghom hhom .compatible = c
    where
    c : compatible-map 𝑨 𝑪 (h ⊙ g)
    c {f}{a} = trans lemg lemh
      where
      lemg : h ⟨$⟩ (g ⟨$⟩ (f ^ 𝑨) a) ≈₃ h ⟨$⟩ (f ^ 𝑩) λ x → g ⟨$⟩ a x
      lemg = h .cong (ghom .compatible)

      lemh : h ⟨$⟩ (f ^ 𝑩) (λ x → g ⟨$⟩ a x) ≈₃ (f ^ 𝑪) λ x → h ⟨$⟩ (g ⟨$⟩ a x)
      lemh = hhom .compatible

  ⊙-hom : hom 𝑨 𝑩 → hom 𝑩 𝑪  → hom 𝑨 𝑪
  ⊙-hom (h , hhom) (g , ghom) = (g ⊙ h) , ⊙-is-hom hhom ghom

  -- The composition of epimorphisms is again an epimorphism
  open IsEpi

  ⊙-is-epi : {g : A ⟶ B}{h : B ⟶ C} → IsEpi 𝑨 𝑩 g → IsEpi 𝑩 𝑪 h → IsEpi 𝑨 𝑪 (h ⊙ g)
  ⊙-is-epi gE hE .isHom = ⊙-is-hom (isHom gE) (isHom hE)
  ⊙-is-epi gE hE .isSurjective = ⊙-IsSurjective (isSurjective gE) (isSurjective hE)

  ⊙-epi : epi 𝑨 𝑩 → epi 𝑩 𝑪  → epi 𝑨 𝑪
  ⊙-epi (h , hepi) (g , gepi) = (g ⊙ h) , ⊙-is-epi hepi gepi
```


##### Lifting and lowering of homs

First we define the identity homomorphism for setoid algebras and then we prove that the operations of lifting and lowering of a setoid algebra are homomorphisms.

```agda
𝒾𝒹 : {𝑨 : Algebra α ρᵃ} → hom 𝑨 𝑨
𝒾𝒹 .proj₁ =  𝑖𝑑
𝒾𝒹 {𝑨 = 𝑨} .proj₂ .compatible = Setoid.reflexive 𝔻[ 𝑨 ] refl 

module _ {𝑨 : Algebra α ρᵃ}{ℓ : Level} where
  open Level using ( lift ; lower )
  open Setoid 𝔻[ 𝑨 ]              using () renaming ( _≈_ to _≈₁_ ; refl to refl₁ )
  open Setoid 𝔻[ Lift-Algˡ 𝑨 ℓ ]  using () renaming ( _≈_ to _≈ˡ_ ; refl to reflˡ)
  open Setoid 𝔻[ Lift-Algʳ 𝑨 ℓ ]  using () renaming ( _≈_ to _≈ʳ_ )

  ToLiftˡ : hom 𝑨 (Lift-Algˡ 𝑨 ℓ)
  ToLiftˡ .proj₁ ⟨$⟩ x = lift x
  ToLiftˡ .proj₁ .cong = id
  ToLiftˡ .proj₂ .compatible = refl₁

  FromLiftˡ : hom (Lift-Algˡ 𝑨 ℓ) 𝑨
  FromLiftˡ .proj₁ ⟨$⟩ x = lower x
  FromLiftˡ .proj₁ .cong = id
  FromLiftˡ .proj₂ .compatible = reflˡ

  ToFromLiftˡ : ∀ b →  ToLiftˡ .proj₁ ⟨$⟩ (FromLiftˡ .proj₁ ⟨$⟩ b) ≈ˡ b
  ToFromLiftˡ _ = refl₁

  FromToLiftˡ : ∀ a → FromLiftˡ .proj₁ ⟨$⟩ (ToLiftˡ .proj₁ ⟨$⟩ a) ≈₁ a
  FromToLiftˡ _ = refl₁

  ToLiftʳ : hom 𝑨 (Lift-Algʳ 𝑨 ℓ)
  ToLiftʳ .proj₁ ⟨$⟩ x = x
  ToLiftʳ .proj₁ .cong = lift
  ToLiftʳ .proj₂ .compatible = lift refl₁

  FromLiftʳ : hom (Lift-Algʳ 𝑨 ℓ) 𝑨
  FromLiftʳ .proj₁ ⟨$⟩ x = x
  FromLiftʳ .proj₁ .cong = lower
  FromLiftʳ .proj₂ .compatible = reflˡ

  ToFromLiftʳ : ∀ b → ToLiftʳ .proj₁ ⟨$⟩ (FromLiftʳ .proj₁ ⟨$⟩ b) ≈ʳ b
  ToFromLiftʳ _ = lift refl₁

  FromToLiftʳ : ∀ a → FromLiftʳ .proj₁ ⟨$⟩ (ToLiftʳ .proj₁ ⟨$⟩ a) ≈₁ a
  FromToLiftʳ _ = refl₁

module _ {𝑨 : Algebra α ρᵃ}{ℓ r : Level} where
  open Setoid 𝔻[ 𝑨 ]               using () renaming (refl to ≈refl)
  open Setoid 𝔻[ Lift-Alg 𝑨 ℓ r ]  using ( _≈_ )

  ToLift : hom 𝑨 (Lift-Alg 𝑨 ℓ r)
  ToLift = ⊙-hom ToLiftˡ ToLiftʳ

  FromLift : hom (Lift-Alg 𝑨 ℓ r) 𝑨
  FromLift = ⊙-hom FromLiftʳ FromLiftˡ

  ToFromLift : ∀ {b} → ToLift .proj₁ ⟨$⟩ (FromLift .proj₁ ⟨$⟩ b) ≈ b
  ToFromLift = Level.lift ≈refl

  ToLift-epi : epi 𝑨 (Lift-Alg 𝑨 ℓ r)
  ToLift-epi =  ToLift .proj₁ ,
                record  { isHom = ToLift .proj₂
                        ; isSurjective = λ {y} → eq (FromLift .proj₁ ⟨$⟩ y) ToFromLift
                        }
```

Next we formalize the fact that a homomorphism from `𝑨` to `𝑩` can be lifted to a
homomorphism from `Lift-Alg 𝑨 ℓᵃ` to `Lift-Alg 𝑩 ℓᵇ`.

```agda
module _ {𝑨 : Algebra α ρᵃ} {𝑩 : Algebra β ρᵇ} where
  open Level using ( lift ; lower )

  Lift-homˡ : hom 𝑨 𝑩  → (ℓᵃ ℓᵇ : Level) →  hom (Lift-Algˡ 𝑨 ℓᵃ) (Lift-Algˡ 𝑩 ℓᵇ)
  Lift-homˡ (f , fhom) ℓᵃ ℓᵇ = ϕ , ⊙-is-hom lABh (ToLiftˡ .proj₂)
    where
    lA : Algebra (α ⊔ ℓᵃ) ρᵃ
    lA = Lift-Algˡ 𝑨 ℓᵃ

    lB : Algebra (β ⊔ ℓᵇ) ρᵇ
    lB = Lift-Algˡ 𝑩 ℓᵇ

    ψ : 𝔻[ lA ] ⟶ 𝔻[ 𝑩 ]
    ψ ⟨$⟩ x = f ⟨$⟩ (Level.lower x)
    ψ .cong = f .cong

    lABh : IsHom lA 𝑩 ψ
    lABh = ⊙-is-hom (FromLiftˡ .proj₂) fhom

    ϕ : 𝔻[ lA ] ⟶ 𝔻[ lB ]
    ϕ ⟨$⟩ x = lift (f ⟨$⟩ (lower x))
    ϕ .cong = f .cong

  Lift-homʳ : hom 𝑨 𝑩  → (rᵃ rᵇ : Level) →  hom (Lift-Algʳ 𝑨 rᵃ) (Lift-Algʳ 𝑩 rᵇ)
  Lift-homʳ (f , fhom) rᵃ rᵇ = ϕ , Goal
    where
    lA : Algebra α (ρᵃ ⊔ rᵃ)
    lA = Lift-Algʳ 𝑨 rᵃ
    lB : Algebra β (ρᵇ ⊔ rᵇ)
    lB = Lift-Algʳ 𝑩 rᵇ
    ψ : 𝔻[ lA ] ⟶ 𝔻[ 𝑩 ]
    ψ ⟨$⟩ x = f ⟨$⟩ x
    ψ .cong = f .cong ∘ lower

    lABh : IsHom lA 𝑩 ψ
    lABh = ⊙-is-hom (proj₂ FromLiftʳ) fhom

    ϕ : 𝔻[ lA ] ⟶ 𝔻[ lB ]
    ϕ ⟨$⟩ x = f ⟨$⟩ x
    ϕ .cong xy .lower = f .cong $ xy .lower

    Goal : IsHom lA lB ϕ
    Goal = ⊙-is-hom lABh (ToLiftʳ .proj₂)

  module _ (h : hom 𝑨 𝑩)(a : 𝕌[ 𝑨 ])(ℓᵃ ℓᵇ : Level) where
    open Setoid 𝔻[ Lift-Algˡ 𝑩 ℓᵇ ] using ( _≈_ )

    lift-hom-lemma : lift (h .proj₁ ⟨$⟩ a) ≈ (Lift-homˡ h ℓᵃ ℓᵇ) .proj₁ ⟨$⟩ lift a
    lift-hom-lemma = Setoid.refl 𝔻[ 𝑩 ]

module _ {𝑨 : Algebra α ρᵃ} {𝑩 : Algebra β ρᵇ} where

  Lift-hom : hom 𝑨 𝑩  → (ℓᵃ rᵃ ℓᵇ rᵇ : Level) → hom (Lift-Alg 𝑨 ℓᵃ rᵃ) (Lift-Alg 𝑩 ℓᵇ rᵇ)
  Lift-hom φ ℓᵃ rᵃ ℓᵇ rᵇ = Lift-homʳ (Lift-homˡ φ ℓᵃ ℓᵇ) rᵃ rᵇ

  Lift-hom-fst : hom 𝑨 𝑩 → (ℓ r : Level) → hom (Lift-Alg 𝑨 ℓ r) 𝑩
  Lift-hom-fst φ _ _ = ⊙-hom FromLift φ

  Lift-hom-snd : hom 𝑨 𝑩 → (ℓ r : Level) → hom 𝑨 (Lift-Alg 𝑩 ℓ r)
  Lift-hom-snd φ _ _ = ⊙-hom φ ToLift
```
