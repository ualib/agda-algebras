---
layout: default
title : "Setoid.Homomorphisms.Basic module (Agda Universal Algebra Library)"
date : "2021-09-13"
author: "agda-algebras development team"
---

#### Homomorphisms of Algebras over Setoids

This is the [Setoid.Homomorphisms.Basic][] module of the [Agda Universal Algebra Library][].


```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature )

module Setoid.Homomorphisms.Basic {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ------------------------------
open import Agda.Primitive           using () renaming ( Set to Type )
open import Data.Product             using ( _,_ ; Σ ; Σ-syntax )
open import Function.Bundles         using () renaming ( Func to _⟶_ )
open import Level                    using ( Level ; _⊔_ )
open import Relation.Binary          using ( Setoid )

-- Imports from the Agda Universal Algebra Library ---------------------------
open import Overture                 using ( proj₁ ; proj₂ ; OperationSymbolsOf )
open import Setoid.Functions         using ( IsInjective ; IsSurjective )
open import Setoid.Algebras {𝑆 = 𝑆}  using ( Algebra ; _^_ ; 𝔻[_])

private variable α β ρᵃ ρᵇ : Level

module _ (𝑨 : Algebra α ρᵃ)(𝑩 : Algebra β ρᵇ) where
  open _⟶_ {a = α}{ρᵃ}{β}{ρᵇ}{From = 𝔻[ 𝑨 ]}{To = 𝔻[ 𝑩 ]} renaming (to to _⟨$⟩_ )

  compatible-map-op : (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) → OperationSymbolsOf 𝑆 → Type (𝓥 ⊔ α ⊔ ρᵇ)
  compatible-map-op h f =  ∀ {a} → h ⟨$⟩ (f ^ 𝑨) a ≈₂ (f ^ 𝑩) λ x → h ⟨$⟩ a x
    where open Setoid 𝔻[ 𝑩 ] using() renaming ( _≈_ to _≈₂_ )

  compatible-map : (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵇ)
  compatible-map h = ∀ {f} → compatible-map-op h f

  -- The property of being a homomorphism.
  record IsHom (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ ρᵇ) where
    constructor mkIsHom
    field compatible : compatible-map h

  hom : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
  hom = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsHom

  -- Smart constructor for a homomorphism: bundle a setoid map with its
  -- compatibility proof, hiding the Σ / IsHom plumbing.
  mkhom : (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) → compatible-map h → hom
  mkhom h c = h , mkIsHom c
```

#### Monomorphisms and epimorphisms

```agda
  record IsMon (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ) where
    field
      isHom : IsHom h
      isInjective : IsInjective h

    HomReduct : hom
    HomReduct = h , isHom

  mon : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
  mon = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsMon

  mon→hom : mon → hom
  mon→hom h = IsMon.HomReduct (proj₂ h)

  record IsEpi (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ) where
    field
      isHom : IsHom h
      isSurjective : IsSurjective h

    HomReduct : hom
    HomReduct = h , isHom

  epi : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
  epi = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsEpi

  epi→hom : epi → hom
  epi→hom h = IsEpi.HomReduct (proj₂ h)

module _ (𝑨 : Algebra α ρᵃ)(𝑩 : Algebra β ρᵇ) where
  open IsEpi
  open IsMon

  mon→intohom : mon 𝑨 𝑩 → Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective (proj₁ h)
  mon→intohom (hh , hhM) = (hh , isHom hhM) , isInjective hhM

  epi→ontohom : epi 𝑨 𝑩 → Σ[ h ∈ hom 𝑨 𝑩 ] IsSurjective (proj₁ h)
  epi→ontohom (hh , hhE) = (hh , isHom hhE) , isSurjective hhE
```


--------------------------------

<span style="float:left;">[↑ Setoid.Homomorphisms](Setoid.Homomorphisms.html)</span>
<span style="float:right;">[Setoid.Homomorphisms.Properties →](Setoid.Homomorphisms.Properties.html)</span>

{% include UALib.Links.md %}


