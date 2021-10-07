---
layout: default
title : "Homomorphisms.Func.Basic module (Agda Universal Algebra Library)"
date : "2021-09-13"
author: "agda-algebras development team"
---

#### <a id="homomorphisms-of-algebras-over-setoids">Homomorphisms of Algebras over Setoids</a>

This is the [Homomorphisms.Func.Basic][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using (𝓞 ; 𝓥 ; Signature )

module Homomorphisms.Func.Basic {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ------------------------------
open import Agda.Primitive    using ( _⊔_ ; Level ) renaming ( Set to Type )
open import Data.Product      using ( _,_ ; Σ )
open import Function.Bundles  using ( Func )
open import Relation.Binary   using ( Setoid )

-- Imports from the Agda Universal Algebra Library ---------------------------
open import Overture.Preliminaries      using ( ∣_∣ ; ∥_∥ )
open import Overture.Func.Preliminaries using ( _⟶_ )
open import Overture.Func.Injective     using ( IsInjective )
open import Overture.Func.Surjective    using ( IsSurjective )
open import Algebras.Func.Basic {𝑆 = 𝑆} using ( SetoidAlgebra ; _̂_ )

private variable
 α β ρᵃ ρᵇ : Level

module _ (𝑨 : SetoidAlgebra α ρᵃ)(𝑩 : SetoidAlgebra β ρᵇ) where
 open SetoidAlgebra 𝑨 using () renaming (Domain to A )
 open SetoidAlgebra 𝑩 using () renaming (Domain to B )
 open Setoid A using () renaming ( _≈_ to _≈₁_ )
 open Setoid B using () renaming ( _≈_ to _≈₂_ )
 open Func {a = α}{ρᵃ}{β}{ρᵇ}{From = A}{To = B} renaming (f to _⟨$⟩_ )

 ≈preserving : (A ⟶ B) → Type (α ⊔ ρᵃ ⊔ ρᵇ)
 ≈preserving f = ∀ {x y} → x ≈₁ y → (f ⟨$⟩ x) ≈₂ (f ⟨$⟩ y)

 compatible-map-op : (A ⟶ B) → ∣ 𝑆 ∣ → Type (𝓥 ⊔ α ⊔ ρᵇ)
 compatible-map-op h f = ∀ {a} → (h ⟨$⟩ ((f ̂ 𝑨) a)) ≈₂ ((f ̂ 𝑩) (λ x → (h ⟨$⟩ (a x))))

 compatible-map : (A ⟶ B) → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵇ)
 compatible-map h = ∀ {f} → compatible-map-op h f

 -- The property of being a homomorphism.
 record IsHom (h : A ⟶ B) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ ρᵇ) where
  field
   compatible : compatible-map h
   -- preserves≈ : ≈preserving h

 hom : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 hom = Σ (A ⟶ B) IsHom

\end{code}


#### <a id="monomorphisms-and-epimorphisms">Monomorphisms and epimorphisms</a>

\begin{code}

 record IsMon (h : A ⟶ B) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ) where
  field
   isHom : IsHom h
   isInjective : IsInjective h

  HomReduct : hom
  HomReduct = h , isHom

 mon : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 mon = Σ (A ⟶ B) IsMon

 mon-to-hom : mon → hom
 mon-to-hom h = ∣ h ∣ , IsMon.isHom ∥ h ∥


 record IsEpi (h : A ⟶ B) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ) where
  field
   isHom : IsHom h
   isSurjective : IsSurjective h

  HomReduct : hom
  HomReduct = h , isHom

 epi : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
 epi = Σ (A ⟶ B) IsEpi

 epi-to-hom : epi → hom
 epi-to-hom h = ∣ h ∣ , (IsEpi.isHom ∥ h ∥)

\end{code}

--------------------------------

<span style="float:left;">[↑ Homomorphisms.Func](Homomorphisms.Func.html)</span>
<span style="float:right;">[Homomorphisms.Func.Properties →](Homomorphisms.Func.Properties.html)</span>

{% include UALib.Links.md %}


