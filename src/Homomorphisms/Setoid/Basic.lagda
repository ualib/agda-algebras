---
layout: default
title : "Homomorphisms.Setoid.Basic module (Agda Universal Algebra Library)"
date : "2021-07-03"
author: "agda-algebras development team"
---

#### <a id="homomorphisms-of-algebras-over-setoids">Homomorphisms of Algebras over Setoids</a>

This is the [Homomorphisms.Setoid.Basic][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using (𝓞 ; 𝓥 ; Signature )

module Homomorphisms.Setoid.Basic {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ------------------------------------------
open import Agda.Primitive    using ( _⊔_ ; lsuc ) renaming ( Set to Type )
open import Data.Product      using ( _,_ ; Σ ; Σ-syntax ; _×_ ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Function          using ( _∘_ ; id ; _on_ ; Func )
open import Level             using ( Level ; Lift )
open import Relation.Binary   using ( IsEquivalence ; Setoid ; REL)
open import Relation.Unary    using ( _⊆_ )
open import Relation.Binary.PropositionalEquality as PE
                              using ( _≡_ ; refl ; module ≡-Reasoning )

-- Imports from the Agda Universal Algebra Library ------------------------------------------
open import Overture.Preliminaries  using ( ∣_∣ ; ∥_∥ ; _⁻¹ ) --  renaming ( _≈_ )
open import Overture.Inverses       using ( IsInjective ; IsSurjective ; SurjInv
                                          ; SurjInvIsRightInv ; epic-factor )
open import Relations.Discrete      using ( ker ; kernel ; kerRel ; kerRelOfEquiv )
open import Relations.Quotients     using ( ker-IsEquivalence )
open import Equality.Welldefined    using ( swelldef )
open import Equality.Truncation     using ( is-set ; blk-uip ; is-embedding
                                          ; monic-is-embedding|Set )
open import Algebras.Setoid.Basic {𝑆 = 𝑆} using ( 𝕌[_] ; SetoidAlgebra ; _̂_ ; Lift-Alg )
open import Algebras.Setoid.Congruences {𝑆 = 𝑆} using ( _∣≈_ ; Con ; IsCongruence ; mkcon ; _╱_)
private variable
 α β γ ρ ρᵃ ρᵇ ρᶜ ℓ : Level

module _ (𝑨 : SetoidAlgebra α ρᵃ) (𝑩 : SetoidAlgebra β ρᵇ) where

 -- non-Setoid-based development (definitions are relative to judgmental equality; i.e., _≡_)
 compatible-op-map : ∣ 𝑆 ∣ → (𝕌[ 𝑨 ] → 𝕌[ 𝑩 ]) → Type (𝓥 ⊔ α ⊔ β)
 compatible-op-map f h = ∀ a → h ((f ̂ 𝑨) a) ≡ ((f ̂ 𝑩) (h ∘ a))

 -- The property of being a homomorphism.
 is-homomorphism : (𝕌[ 𝑨 ] → 𝕌[ 𝑩 ]) → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
 is-homomorphism h = ∀ f  →  compatible-op-map f h

 -- The type of homomorphisms from `𝑨` to `𝑩`.
 hom : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β)
 hom = Σ (𝕌[ 𝑨 ] → 𝕌[ 𝑩 ]) is-homomorphism

 -- Setoid-based development (definitions are relative to setoid equality)
 open SetoidAlgebra
 open Setoid

 ≈preserving : (𝕌[ 𝑨 ] → 𝕌[ 𝑩 ]) → Type (α ⊔ ρᵃ ⊔ ρᵇ)
 ≈preserving f = ∀ {x y} → (_≈_ (Domain 𝑨)) x y → (_≈_ (Domain 𝑩)) (f x) (f y)
 compatible-map-op : (𝕌[ 𝑨 ] → 𝕌[ 𝑩 ]) → ∣ 𝑆 ∣ → Type (𝓥 ⊔ α ⊔ ρᵇ)
 compatible-map-op h f = ∀ a → (_≈_ (Domain 𝑩)) (h ((f ̂ 𝑨) a)) ((f ̂ 𝑩) (h ∘ a))

 compatible-map : (𝕌[ 𝑨 ] → 𝕌[ 𝑩 ]) → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵇ)
 compatible-map h = ∀ f → compatible-map-op h f


 -- The property of being a homomorphism.
 record IsHom (map : 𝕌[ 𝑨 ] → 𝕌[ 𝑩 ]) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ ρᵇ) where
  field
   compatible : compatible-map map
   congruent : ≈preserving map

 Hom : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 Hom = Σ (𝕌[ 𝑨 ] → 𝕌[ 𝑩 ]) IsHom

\end{code}

##### <a id="composition-of-homs">Composition of homs</a>

\begin{code}

open ≡-Reasoning

module _ (𝑨 : SetoidAlgebra α ρᵃ)
         (𝑩 : SetoidAlgebra β ρᵇ)
         (𝑪 : SetoidAlgebra γ ρᶜ)
         where

 -- non-setoid-based development
 -- The composition of homomorphisms is again a homomorphism.
 ∘-is-hom : {g : 𝕌[ 𝑨 ] → 𝕌[ 𝑩 ]}{h : 𝕌[ 𝑩 ] → 𝕌[ 𝑪 ]}
  →         is-homomorphism 𝑨 𝑩 g → is-homomorphism 𝑩 𝑪 h
            -------------------------------------------------
  →         is-homomorphism 𝑨 𝑪 (h ∘ g)

 ∘-is-hom {g} {h} ghom hhom 𝑓 a = (h ∘ g)((𝑓 ̂ 𝑨) a) ≡⟨ PE.cong h ( ghom 𝑓 a ) ⟩
                                  h ((𝑓 ̂ 𝑩)(g ∘ a)) ≡⟨ hhom 𝑓 ( g ∘ a ) ⟩
                                  (𝑓 ̂ 𝑪)(h ∘ g ∘ a) ∎

 ∘-hom : hom 𝑨 𝑩  →  hom 𝑩 𝑪  →  hom 𝑨 𝑪
 ∘-hom (g , ghom) (h , hhom) = h ∘ g , ∘-is-hom {g}{h} ghom hhom


 -- setoid-based development
 open Setoid
 open SetoidAlgebra
 open IsHom
 -- The composition of homomorphisms is again a homomorphism
 ∘IsHom : {g : 𝕌[ 𝑨 ] → 𝕌[ 𝑩 ]}{h : 𝕌[ 𝑩 ] → 𝕌[ 𝑪 ]}
  →         IsHom 𝑨 𝑩 g → IsHom 𝑩 𝑪 h
            -------------------------------------------------
  →         IsHom 𝑨 𝑪 (h ∘ g)

 ∘IsHom {g} {h} ghom hhom = record { compatible = i ; congruent = ii }
  where
  i : compatible-map 𝑨 𝑪 (h ∘ g)
  i f a = trans (Domain 𝑪) lemg lemh
   where
   lemg : (_≈_ (Domain 𝑪)) (h (g ((f ̂ 𝑨) a))) (h ((f ̂ 𝑩) (λ x → g (a x))))
   lemg = congruent hhom (compatible ghom f a)

   lemh : (_≈_ (Domain 𝑪)) (h ((f ̂ 𝑩) (λ x → g (a x)))) ((f ̂ 𝑪) (λ x → h (g (a x))))
   lemh = compatible hhom f (g ∘ a)


  ii : ≈preserving 𝑨 𝑪 (h ∘ g)
  ii xy = congruent hhom (congruent ghom xy)

 ∘Hom : Hom 𝑨 𝑩 → Hom 𝑩 𝑪  → Hom 𝑨 𝑪
 ∘Hom (h , hhom) (g , ghom) = (g ∘ h) , ∘IsHom hhom ghom

\end{code}



##### <a id="lifting-and-lowering">Lifting and lowering of homs</a>

First we define the identity homomorphism for setoid algebras and then we prove that the operations of lifting and lowering of a setoid algebra are homomorphisms.

\begin{code}

-- non-setoid-based version

𝒾𝒹 :  (𝑨 : SetoidAlgebra α ρ) → hom 𝑨 𝑨
𝒾𝒹 𝑨 = id , λ 𝑓 a →  refl

open Level
𝓁𝒾𝒻𝓉 : {𝑨 : SetoidAlgebra α ρ} → hom 𝑨 (Lift-Alg 𝑨 ℓ)
𝓁𝒾𝒻𝓉 = lift , (λ 𝑓 a → refl)

𝓁ℴ𝓌ℯ𝓇 : {𝑨 : SetoidAlgebra α ρ} → hom (Lift-Alg 𝑨 ℓ) 𝑨
𝓁ℴ𝓌ℯ𝓇 = lower , λ 𝑓 a → refl

\end{code}

Next we formalize the fact that a homomorphism from `𝑨` to `𝑩` can be lifted to a homomorphism from `Lift-Alg 𝑨 ℓᵃ` to `Lift-Alg 𝑩 ℓᵇ`.

\begin{code}

module _ {𝑨 : SetoidAlgebra α ρᵃ} {𝑩 : SetoidAlgebra β ρᵇ} where
 open Level

 Lift-hom : hom 𝑨 𝑩  → (ℓᵃ ℓᵇ : Level) →  hom (Lift-Alg 𝑨 ℓᵃ) (Lift-Alg 𝑩 ℓᵇ)
 Lift-hom (f , fhom) ℓᵃ ℓᵇ = lift ∘ f ∘ lower , Goal
  where
  lA lB : SetoidAlgebra _ _
  lA = Lift-Alg 𝑨 ℓᵃ
  lB = Lift-Alg 𝑩 ℓᵇ

  lABh : is-homomorphism lA 𝑩 (f ∘ lower)
  lABh = ∘-is-hom lA 𝑨  𝑩 {lower}{f} (λ _ _ → refl) fhom

  Goal : is-homomorphism lA lB (lift ∘ (f ∘ lower))
  Goal = ∘-is-hom lA 𝑩 lB {f ∘ lower}{lift} lABh λ _ _ → refl

-- setoid-based version
open SetoidAlgebra

ℐ𝒹 :  (𝑨 : SetoidAlgebra α ρ) → Hom 𝑨 𝑨
ℐ𝒹 𝑨 = id , record { compatible = λ f a → Setoid.reflexive (Domain 𝑨) refl
                    ; congruent = id }

open Level
ℒ𝒾𝒻𝓉 : {𝑨 : SetoidAlgebra α ρ} → Hom 𝑨 (Lift-Alg 𝑨 ℓ)
ℒ𝒾𝒻𝓉 {𝑨 = 𝑨} = lift , record { compatible = λ f a → Setoid.reflexive (Domain 𝑨) refl
                              ; congruent = id }

ℒℴ𝓌ℯ𝓇 : {𝑨 : SetoidAlgebra α ρ} → Hom (Lift-Alg 𝑨 ℓ) 𝑨
ℒℴ𝓌ℯ𝓇 {ℓ = ℓ}{𝑨} = lower , record { compatible = λ f a → Setoid.reflexive (Domain (Lift-Alg 𝑨 ℓ)) refl
                                    ; congruent = id }


module _ {𝑨 : SetoidAlgebra α ρᵃ} {𝑩 : SetoidAlgebra β ρᵇ} where
 open Level

 LiftHom : Hom 𝑨 𝑩  → (ℓᵃ ℓᵇ : Level) →  Hom (Lift-Alg 𝑨 ℓᵃ) (Lift-Alg 𝑩 ℓᵇ)
 LiftHom (f , fhom) ℓᵃ ℓᵇ = (lift ∘ f ∘ lower) , Goal
  where
  lA lB : SetoidAlgebra _ _
  lA = Lift-Alg 𝑨 ℓᵃ
  lB = Lift-Alg 𝑩 ℓᵇ

  lABh : IsHom lA 𝑩 (f ∘ lower)
  lABh = ∘IsHom lA 𝑨 𝑩 (snd ℒℴ𝓌ℯ𝓇) fhom

  Goal : IsHom lA lB (lift ∘ (f ∘ lower))
  Goal = ∘IsHom lA 𝑩 lB lABh (snd ℒ𝒾𝒻𝓉)

\end{code}



#### <a id="monomorphisms-and-epimorphisms">Monomorphisms and epimorphisms</a>

\begin{code}

module _ (𝑨 : SetoidAlgebra α ρᵃ) (𝑩 : SetoidAlgebra β ρᵇ) where
 private
  A = 𝕌[ 𝑨 ]  -- carrier of Domain 𝑨
  B = 𝕌[ 𝑩 ]  -- carrier of Domain 𝑩

 is-monomorphism : (A → B) → Type _
 is-monomorphism g = is-homomorphism 𝑨 𝑩 g × IsInjective g

 is-epimorphism : (A → B) → Type _
 is-epimorphism g = is-homomorphism 𝑨 𝑩 g × IsSurjective g

record mon (𝑨 : SetoidAlgebra α ρᵃ)
           (𝑩 : SetoidAlgebra β ρᵇ) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β ⊔ ρᵇ) where
 field
  map : 𝕌[ 𝑨 ] → 𝕌[ 𝑩 ]
  is-mon : is-monomorphism 𝑨 𝑩 map

 mon-to-hom : hom 𝑨 𝑩
 mon-to-hom = map , ∣ is-mon ∣

record epi (𝑨 : SetoidAlgebra α ρᵃ)
           (𝑩 : SetoidAlgebra β ρᵇ) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β ⊔ ρᵇ) where
 field
  map : 𝕌[ 𝑨 ] → 𝕌[ 𝑩 ]
  is-epi : is-epimorphism 𝑨 𝑩 map

 epi-to-hom : hom 𝑨 𝑩
 epi-to-hom = map , ∣ is-epi ∣


-- setoid-based version
module _ (𝑨 : SetoidAlgebra α ρᵃ) (𝑩 : SetoidAlgebra β ρᵇ) where
 private
  A = 𝕌[ 𝑨 ]  -- carrier of Domain 𝑨
  B = 𝕌[ 𝑩 ]  -- carrier of Domain 𝑩

 record IsMon (map : A → B) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ) where
  field
   isHom : IsHom 𝑨 𝑩 map
   isInjective : IsInjective map

  HomReduct : Hom 𝑨 𝑩
  HomReduct = map , isHom

 Mon : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 Mon = Σ (A → B) IsMon

 -- Mon→Hom : Mon → Hom

 record IsEpi (map : A → B) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ) where
  field
   isHom : IsHom 𝑨 𝑩 map
   isSurjective : IsSurjective map

  HomReduct : Hom 𝑨 𝑩
  HomReduct = map , isHom

 Epi : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 Epi = Σ (A → B) IsEpi

\end{code}

#### <a id="kernels-of-homomorphisms">Kernels of homomorphisms</a>

\begin{code}

module _ (𝑨 : SetoidAlgebra α ρᵃ) (𝑩 : SetoidAlgebra β ρᵇ) where
 private
  A = 𝕌[ 𝑨 ]
  B = 𝕌[ 𝑩 ]

 homker-comp : swelldef 𝓥 β → (h : hom 𝑨 𝑩) → 𝑨 ∣≈ (ker ∣ h ∣)
 homker-comp wd h f {u}{v} kuv = ∣ h ∣((f ̂ 𝑨) u)   ≡⟨ ∥ h ∥ f u ⟩
                                 (f ̂ 𝑩)(∣ h ∣ ∘ u) ≡⟨ wd(f ̂ 𝑩)(∣ h ∣ ∘ u)(∣ h ∣ ∘ v)kuv ⟩
                                 (f ̂ 𝑩)(∣ h ∣ ∘ v) ≡⟨ (∥ h ∥ f v)⁻¹ ⟩
                                 ∣ h ∣((f ̂ 𝑨) v)   ∎

 kercon : swelldef 𝓥 β → hom 𝑨 𝑩 → Con 𝑨
 kercon wd h = ker ∣ h ∣ , mkcon (ker-IsEquivalence ∣ h ∣) (homker-comp wd h)

 kerquo : swelldef 𝓥 β → hom 𝑨 𝑩 → SetoidAlgebra _ _
 kerquo wd h = 𝑨 ╱ (kercon wd h)

ker[_⇒_]_↾_ : (𝑨 : SetoidAlgebra α ρᵃ) (𝑩 : SetoidAlgebra β ρᵇ)
 →            hom 𝑨 𝑩 → swelldef 𝓥 β → SetoidAlgebra _ _
ker[ 𝑨 ⇒ 𝑩 ] h ↾ wd = kerquo 𝑨 𝑩 wd h



-- setoid version

module _ (𝑨 : SetoidAlgebra α ρᵃ) (𝑩 : SetoidAlgebra β ρᵇ) where
 open SetoidAlgebra
 open Setoid
 open Func
 private
  A = 𝕌[ 𝑨 ]
  B = 𝕌[ 𝑩 ]
  ≈B = _≈_ (Domain 𝑩)
 HomKerComp : (h : Hom 𝑨 𝑩) → 𝑨 ∣≈ (kerRel ≈B ∣ h ∣)
 HomKerComp h f {u}{v} kuv = Goal
  where
  fhuv : ≈B ((f ̂ 𝑩)(∣ h ∣ ∘ u)) ((f ̂ 𝑩)(∣ h ∣ ∘ v))
  fhuv = cong (Interp 𝑩) (PE.refl , kuv)
  lem1 : ≈B (∣ h ∣ ((f ̂ 𝑨) u)) ((f ̂ 𝑩) (∣ h ∣ ∘ u))
  lem1 = IsHom.compatible ∥ h ∥ f u

  lem2 : ≈B ((f ̂ 𝑩) (∣ h ∣ ∘ v)) (∣ h ∣ ((f ̂ 𝑨) v))
  lem2 = (sym (Domain 𝑩)) (IsHom.compatible ∥ h ∥ f v)
  Goal : ≈B (∣ h ∣ ((f ̂ 𝑨) u)) (∣ h ∣ ((f ̂ 𝑨) v))
  Goal = trans (Domain 𝑩) lem1 (trans (Domain 𝑩) fhuv lem2)

 KerCon : Hom 𝑨 𝑩 → Con 𝑨
 KerCon h = (kerRel ≈B ∣ h ∣) , mkcon (kerRelOfEquiv (isEquivalence (Domain 𝑩)) ∣ h ∣) (HomKerComp h)

 KerQuo : Hom 𝑨 𝑩 → SetoidAlgebra _ _
 KerQuo h = 𝑨 ╱ (KerCon h)

Ker[_⇒_]_ : (𝑨 : SetoidAlgebra α ρᵃ) (𝑩 : SetoidAlgebra β ρᵇ)
 →          Hom 𝑨 𝑩 → SetoidAlgebra _ _
Ker[ 𝑨 ⇒ 𝑩 ] h = KerQuo 𝑨 𝑩 h
\end{code}

--------------------------------

<span style="float:left;">[↑ Homomorphisms.Setoid](Homomorphisms.Setoid.html)</span>
<span style="float:right;">[Homomorphisms.Setoid.Noether →](Homomorphisms.Setoid.Noether.html)</span>

{% include UALib.Links.md %}
