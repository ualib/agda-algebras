---
layout: default
title : Setoid."Homomorphisms.Properties module (Agda Universal Algebra Library)"
date : "2021-09-13"
author: "agda-algebras development team"
---

#### <a id="properties-of-homomorphisms-of-setoidalgebras">Properties of Homomorphisms of Algebras</a>

This is the [Setoid.Homomorphisms.Properties][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Homomorphisms.Properties {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ------------------------------------------
open import Data.Product     using ( _,_ ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Function         using ( id ; _$_ ) renaming ( Func to _⟶_ )
open import Level            using ( Level )
open import Relation.Binary  using ( Setoid )

open import Relation.Binary.PropositionalEquality as ≡ using ( _≡_ )

-- Imports from the Agda Universal Algebra Library ------------------------------------------
open import Overture          using ( ∣_∣ ; ∥_∥ )
open import Setoid.Functions  using ( _⊙_ ; 𝑖𝑑 ; Image_∋_ ; eq ; ⊙-IsSurjective )

open  import Setoid.Algebras {𝑆 = 𝑆}
      using ( Algebra ; _̂_; Lift-Algˡ; Lift-Algʳ; Lift-Alg; 𝕌[_])
open  import Setoid.Homomorphisms.Basic {𝑆 = 𝑆}
      using ( hom ; IsHom ; epi ; IsEpi ; compatible-map )

open _⟶_ using ( cong ) renaming ( to to _⟨$⟩_ )

private variable α β γ ρᵃ ρᵇ ρᶜ ℓ : Level
\end{code}

##### <a id="composition-of-homs">Composition of homs</a>

\begin{code}

module _  {𝑨 : Algebra α ρᵃ} {𝑩 : Algebra β ρᵇ} {𝑪 : Algebra γ ρᶜ} where
  open Algebra 𝑨  renaming (Domain to A )   using ()
  open Algebra 𝑩  renaming (Domain to B )   using ()
  open Algebra 𝑪  renaming (Domain to C )   using ()
  open Setoid A   renaming ( _≈_ to _≈₁_ )  using ()
  open Setoid B   renaming ( _≈_ to _≈₂_ )  using ()
  open Setoid C   renaming ( _≈_ to _≈₃_ )  using ( trans )

  open IsHom

  -- The composition of homomorphisms is again a homomorphism
  ⊙-is-hom :  {g : A ⟶ B}{h : B ⟶ C}
   →          IsHom 𝑨 𝑩 g → IsHom 𝑩 𝑪 h
   →          IsHom 𝑨 𝑪 (h ⊙ g)

  ⊙-is-hom {g} {h} ghom hhom = record { compatible = c }
   where
   c : compatible-map 𝑨 𝑪 (h ⊙ g)
   c {f}{a} = trans lemg lemh
    where
    lemg : (h ⟨$⟩ (g ⟨$⟩ ((f ̂ 𝑨) a))) ≈₃ (h ⟨$⟩ ((f ̂ 𝑩) (λ x → g ⟨$⟩ (a x))))
    lemg = cong h (compatible ghom)

    lemh : (h ⟨$⟩ ((f ̂ 𝑩) (λ x → g ⟨$⟩ (a x)))) ≈₃ ((f ̂ 𝑪) (λ x → h ⟨$⟩ (g ⟨$⟩ (a x))))
    lemh = compatible hhom

  ⊙-hom : hom 𝑨 𝑩 → hom 𝑩 𝑪  → hom 𝑨 𝑪
  ⊙-hom (h , hhom) (g , ghom) = (g ⊙ h) , ⊙-is-hom hhom ghom

  -- The composition of epimorphisms is again an epimorphism
  open IsEpi

  ⊙-is-epi :  {g : A ⟶ B}{h : B ⟶ C}
   →          IsEpi 𝑨 𝑩 g → IsEpi 𝑩 𝑪 h → IsEpi 𝑨 𝑪 (h ⊙ g)

  ⊙-is-epi gE hE = record  { isHom = ⊙-is-hom (isHom gE) (isHom hE)
                           ; isSurjective = ⊙-IsSurjective (isSurjective gE) (isSurjective hE)
                           }

  ⊙-epi : epi 𝑨 𝑩 → epi 𝑩 𝑪  → epi 𝑨 𝑪
  ⊙-epi (h , hepi) (g , gepi) = (g ⊙ h) , ⊙-is-epi hepi gepi
\end{code}


##### <a id="lifting-and-lowering">Lifting and lowering of homs</a>

First we define the identity homomorphism for setoid algebras and then we prove that the operations of lifting and lowering of a setoid algebra are homomorphisms.

\begin{code}

module _ {𝑨 : Algebra α ρᵃ} where
 open Algebra 𝑨  renaming (Domain to A )                   using ()
 open Setoid A   renaming ( _≈_ to _≈₁_ ; refl to refl₁ )  using ( reflexive )

 𝒾𝒹 :  hom 𝑨 𝑨
 𝒾𝒹 = 𝑖𝑑 , record { compatible = reflexive ≡.refl }

module _ {𝑨 : Algebra α ρᵃ}{ℓ : Level} where
 open Algebra 𝑨  using ()             renaming (Domain to A )
 open Setoid A   using ( reflexive )  renaming ( _≈_ to _≈₁_ ; refl to refl₁ )

 open Algebra  using ( Domain )
 open Setoid (Domain (Lift-Algˡ 𝑨 ℓ))  using () renaming ( _≈_ to _≈ˡ_ ; refl to reflˡ)
 open Setoid (Domain (Lift-Algʳ 𝑨 ℓ))  using () renaming ( _≈_ to _≈ʳ_ ; refl to reflʳ)

 open Level
 ToLiftˡ : hom 𝑨 (Lift-Algˡ 𝑨 ℓ)
 ToLiftˡ =  record { to = lift ; cong = id } ,
            record { compatible = reflexive ≡.refl }

 FromLiftˡ : hom (Lift-Algˡ 𝑨 ℓ) 𝑨
 FromLiftˡ = record { to = lower ; cong = id } , record { compatible = reflˡ }

 ToFromLiftˡ : ∀ b →  (∣ ToLiftˡ ∣ ⟨$⟩ (∣ FromLiftˡ ∣ ⟨$⟩ b)) ≈ˡ b
 ToFromLiftˡ b = refl₁

 FromToLiftˡ : ∀ a → (∣ FromLiftˡ ∣ ⟨$⟩ (∣ ToLiftˡ ∣ ⟨$⟩ a)) ≈₁ a
 FromToLiftˡ a = refl₁

 ToLiftʳ : hom 𝑨 (Lift-Algʳ 𝑨 ℓ)
 ToLiftʳ =  record { to = id ; cong = lift } ,
            record { compatible = lift (reflexive ≡.refl) }

 FromLiftʳ : hom (Lift-Algʳ 𝑨 ℓ) 𝑨
 FromLiftʳ =  record { to = id ; cong = lower } , record { compatible = reflˡ }

 ToFromLiftʳ : ∀ b → (∣ ToLiftʳ ∣ ⟨$⟩ (∣ FromLiftʳ ∣ ⟨$⟩ b)) ≈ʳ b
 ToFromLiftʳ b = lift refl₁

 FromToLiftʳ : ∀ a → (∣ FromLiftʳ ∣ ⟨$⟩ (∣ ToLiftʳ ∣ ⟨$⟩ a)) ≈₁ a
 FromToLiftʳ a = refl₁

module _ {𝑨 : Algebra α ρᵃ}{ℓ r : Level} where
 open Level
 open Algebra                            using ( Domain )
 open Setoid  (Domain 𝑨)                 using (refl)
 open Setoid  (Domain (Lift-Alg 𝑨 ℓ r))  using ( _≈_ )

 ToLift : hom 𝑨 (Lift-Alg 𝑨 ℓ r)
 ToLift = ⊙-hom ToLiftˡ ToLiftʳ

 FromLift : hom (Lift-Alg 𝑨 ℓ r) 𝑨
 FromLift = ⊙-hom FromLiftʳ FromLiftˡ

 ToFromLift : ∀ b → (∣ ToLift ∣ ⟨$⟩ (∣ FromLift ∣ ⟨$⟩ b)) ≈ b
 ToFromLift b = lift refl


 ToLift-epi : epi 𝑨 (Lift-Alg 𝑨 ℓ r)
 ToLift-epi = ∣ ToLift ∣ ,
              record  { isHom = ∥ ToLift ∥
                      ; isSurjective = λ {y} → eq (∣ FromLift ∣ ⟨$⟩ y) (ToFromLift y)
                      }

\end{code}

Next we formalize the fact that a homomorphism from `𝑨` to `𝑩` can be lifted to a homomorphism from `Lift-Alg 𝑨 ℓᵃ` to `Lift-Alg 𝑩 ℓᵇ`.

\begin{code}

module _ {𝑨 : Algebra α ρᵃ} {𝑩 : Algebra β ρᵇ} where
 open Algebra            using ( Domain )
 open Setoid (Domain 𝑨)  using ( reflexive )  renaming ( _≈_ to _≈₁_ )
 open Setoid (Domain 𝑩)  using ()             renaming ( _≈_ to _≈₂_ )
 open Level

 Lift-homˡ : hom 𝑨 𝑩  → (ℓᵃ ℓᵇ : Level) →  hom (Lift-Algˡ 𝑨 ℓᵃ) (Lift-Algˡ 𝑩 ℓᵇ)
 Lift-homˡ (f , fhom) ℓᵃ ℓᵇ = ϕ , ⊙-is-hom lABh (snd ToLiftˡ)
  where
  lA lB : Algebra _ _
  lA = Lift-Algˡ 𝑨 ℓᵃ
  lB = Lift-Algˡ 𝑩 ℓᵇ

  ψ : Domain lA ⟶ Domain 𝑩
  ψ ⟨$⟩ x = f ⟨$⟩ (lower x)
  cong ψ = cong f

  lABh : IsHom lA 𝑩 ψ
  lABh = ⊙-is-hom (snd FromLiftˡ) fhom

  ϕ : Domain lA ⟶ Domain lB
  ϕ ⟨$⟩ x = lift (f ⟨$⟩ (lower x))
  cong ϕ = cong f

 Lift-homʳ : hom 𝑨 𝑩  → (rᵃ rᵇ : Level) →  hom (Lift-Algʳ 𝑨 rᵃ) (Lift-Algʳ 𝑩 rᵇ)
 Lift-homʳ (f , fhom) rᵃ rᵇ = ϕ , Goal
  where
  lA lB : Algebra _ _
  lA = Lift-Algʳ 𝑨 rᵃ
  lB = Lift-Algʳ 𝑩 rᵇ
  ψ : Domain lA ⟶ Domain 𝑩
  ψ ⟨$⟩ x = f ⟨$⟩ x
  cong ψ xy = cong f (lower xy)

  lABh : IsHom lA 𝑩 ψ
  lABh = ⊙-is-hom (snd FromLiftʳ) fhom

  ϕ : Domain lA ⟶ Domain lB
  ϕ ⟨$⟩ x = f ⟨$⟩ x
  lower (cong ϕ xy) = cong f $ lower xy

  Goal : IsHom lA lB ϕ
  Goal = ⊙-is-hom lABh (snd ToLiftʳ)

 open Setoid using ( _≈_ )

 lift-hom-lemma :  (h : hom 𝑨 𝑩)(a : 𝕌[ 𝑨 ])(ℓᵃ ℓᵇ : Level)
  →                (_≈_ (Domain (Lift-Algˡ 𝑩 ℓᵇ))) (lift (∣ h ∣ ⟨$⟩ a))
                   (∣ Lift-homˡ h ℓᵃ ℓᵇ ∣ ⟨$⟩ lift a)

 lift-hom-lemma h a ℓᵃ ℓᵇ = Setoid.refl (Domain 𝑩)

module _ {𝑨 : Algebra α ρᵃ} {𝑩 : Algebra β ρᵇ} where

 Lift-hom :  hom 𝑨 𝑩  → (ℓᵃ rᵃ ℓᵇ rᵇ : Level)
  →          hom (Lift-Alg 𝑨 ℓᵃ rᵃ) (Lift-Alg 𝑩 ℓᵇ rᵇ)

 Lift-hom φ ℓᵃ rᵃ ℓᵇ rᵇ = Lift-homʳ (Lift-homˡ φ ℓᵃ ℓᵇ) rᵃ rᵇ

 Lift-hom-fst : hom 𝑨 𝑩  → (ℓ r : Level) →  hom (Lift-Alg 𝑨 ℓ r) 𝑩
 Lift-hom-fst φ _ _ = ⊙-hom FromLift φ

 Lift-hom-snd : hom 𝑨 𝑩  → (ℓ r : Level) →  hom 𝑨 (Lift-Alg 𝑩 ℓ r)
 Lift-hom-snd φ _ _ = ⊙-hom φ ToLift
\end{code}

--------------------------------

<span style="float:left;">[← Setoid.Homomorphisms.Basic](Setoid.Homomorphisms.Basic.html)</span>
<span style="float:right;">[Setoid.Homomorphisms.Kernels →](Setoid.Homomorphisms.Kernels.html)</span>

{% include UALib.Links.md %}
