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

-- Imports from Agda and the Agda Standard Library ------------------------------
open import Agda.Primitive    using ( _⊔_ ) renaming ( Set to Type )
open import Data.Product      using ( _,_ ; Σ )
open import Function          using ( _∘_ )
open import Function.Bundles as FB using ( Func )
open import Function.Equality using ( Π ; _⟶_ )
open import Function.Definitions using ( Injective )
open import Level             using ( Level )
open import Relation.Binary   using ( Setoid )

-- -- Imports from the Agda Universal Algebra Library ---------------------------
open import Overture.Preliminaries        using ( ∣_∣ )
open import Overture.Func.Injective     using ( IsInjective )
open import Overture.Func.Surjective    using ( IsSurjective )
open import Algebras.Setoid.Basic {𝑆 = 𝑆} using ( 𝕌[_] ; SetoidAlgebra ; _̂_ )

private variable
 α β ρᵃ ρᵇ : Level

module _ (𝑨 : SetoidAlgebra α ρᵃ)(𝑩 : SetoidAlgebra β ρᵇ) where
 open SetoidAlgebra 𝑨 using () renaming (Domain to A )
 open SetoidAlgebra 𝑩 using () renaming (Domain to B )
-- open SetoidAlgebra
 open Setoid A using () renaming ( _≈_ to _≈₁_ )
 open Setoid B using () renaming ( _≈_ to _≈₂_ )
 open Π
 open Func {a = α}{ρᵃ}{β}{ρᵇ}{From = A}{To = B} renaming (f to _⟨$⟩_ )

 -- private
 --  A = Domain 𝑨
 --  B = Domain 𝑩
 --  _≈A_ = _≈_ A
 --  _≈B_ = _≈_ B

 ≈preserving : (A ⟶ B) → Type (α ⊔ ρᵃ ⊔ ρᵇ)
 ≈preserving f = ∀ {x y} → x ≈₁ y → (f ⟨$⟩ x) ≈₂ (f ⟨$⟩ y)

 ≈preserving' : Func A B → Type (α ⊔ ρᵃ ⊔ ρᵇ)
 ≈preserving' f = ∀ {x y} → x ≈₁ y → (f ⟨$⟩ x) ≈₂ (f ⟨$⟩ y)

 compatible-map-op : (A ⟶ B) → ∣ 𝑆 ∣ → Type (𝓥 ⊔ α ⊔ ρᵇ)
 compatible-map-op h f = ∀ a → (h ⟨$⟩ ((f ̂ 𝑨) a)) ≈₂ ((f ̂ 𝑩) (λ x → (h ⟨$⟩ (a x))))

 compatible-map : (A ⟶ B) → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵇ)
 compatible-map h = ∀ f → compatible-map-op h f

 -- The property of being a homomorphism.
 record IsHom (h : A ⟶ B) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ ρᵇ) where
  field
   compatible : compatible-map h
   preserves≈ : ≈preserving h

 hom : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 hom = Σ (A ⟶ B) IsHom

\end{code}


#### <a id="monomorphisms-and-epimorphisms">Monomorphisms and epimorphisms</a>

\begin{code}

 record IsMon (h : A ⟶ B) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ) where
  field
   isHom : IsHom h
   isInjective : IsInjective h

  HomReduct : hom 𝑨 𝑩
  HomReduct = h , isHom

 mon : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 mon = Σ (A ⟶ B) IsMon

 record IsEpi (h : A ⟶ B) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ) where
  field
   isHom : IsHom 𝑨 𝑩 h
   isSurjective : IsSurjective h

  HomReduct : hom 𝑨 𝑩
  HomReduct = h , isHom

 epi : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 epi = Σ (A ⟶ B) IsEpi

\end{code}

--------------------------------

<span style="float:left;">[↑ Homomorphisms.Setoid](Homomorphisms.Setoid.html)</span>
<span style="float:right;">[Homomorphisms.Setoid.Properties →](Homomorphisms.Setoid.Properties.html)</span>

{% include UALib.Links.md %}






<!--
 ≈preserving' : (𝕌[ 𝑨 ] → 𝕌[ 𝑩 ]) → Type (α ⊔ ρᵃ ⊔ ρᵇ)
 ≈preserving' f = ∀ {x y} → x ≈₁ y → (f x) ≈B (f y)

 compatible-map-op' : (𝕌[ 𝑨 ] → 𝕌[ 𝑩 ]) → ∣ 𝑆 ∣ → Type (𝓥 ⊔ α ⊔ ρᵇ)
 compatible-map-op' h f = ∀ a → h ((f ̂ 𝑨) a) ≈B (f ̂ 𝑩) (h ∘ a)

 compatible-map' : (𝕌[ 𝑨 ] → 𝕌[ 𝑩 ]) → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵇ)
 compatible-map' h = ∀ f → compatible-map-op' h f

-->
