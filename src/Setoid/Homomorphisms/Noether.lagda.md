---
layout: default
title : "Setoid.Homomorphisms.Noether module (The Agda Universal Algebra Library)"
date : "2021-09-15"
author: "agda-algebras development team"
---

### Homomorphism Theorems for Setoid Algebras

This is the [Setoid.Homomorphisms.Noether][] module of the [Agda Universal Algebra Library][].

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Homomorphisms.Noether {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ---------------------------
open import Data.Product     renaming ( _×_ to _∧_)    using (Σ-syntax ; _,_ )
open import Function         renaming ( Func to _⟶_ )  using ( id )
open import Level                                      using ( Level )
open import Relation.Binary                            using ( Setoid )

open import Relation.Binary.PropositionalEquality      using ( _≡_ ; refl )

-- Imports from agda-algebras ------------------------------------------------
open import Overture                              using ( proj₁ ; proj₂ )
open import Setoid.Functions                      using ( IsInjective )

open import Setoid.Algebras {𝑆 = 𝑆}               using ( Algebra ; 𝔻[_] )
open import Setoid.Homomorphisms.Basic {𝑆 = 𝑆}    using ( hom ; IsHom )
open import Setoid.Homomorphisms.Kernels {𝑆 = 𝑆}  using ( kerquo ; πker )

private variable α ρᵃ β ρᵇ γ ρᶜ ι : Level
```

#### The First Homomorphism Theorem for setoid algebras

```agda
open _⟶_ using ( cong ) renaming ( to to _⟨$⟩_ )

module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}(hh : hom 𝑨 𝑩) where
  open Algebra 𝑩 using ( Interp ) -- renaming ( Domain to B )
  open Setoid 𝔻[ 𝑩 ] using ( _≈_ ) renaming (refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open Algebra (kerquo hh) using () renaming ( Domain to A/hKer )

  open IsHom
  private
    hfunc : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]
    hfunc = hh .proj₁
    h = _⟨$⟩_ hfunc

  FirstHomTheorem : Σ[ (φ , _) ∈ hom (kerquo hh) 𝑩  ]
                     ( ∀ a → h a ≈ φ ⟨$⟩ (πker hh .proj₁ ⟨$⟩ a) ) ∧ IsInjective φ

  FirstHomTheorem = (φ , φhom) , (λ _ → ≈refl) , φmon
    where
    φ : A/hKer ⟶ 𝔻[ 𝑩 ]
    φ ⟨$⟩ x = h x
    φ .cong = id

    φhom : IsHom (kerquo hh) 𝑩 φ
    φhom .compatible = ≈trans (hh .proj₂ .compatible) (cong Interp (refl , (λ _ → ≈refl)))

    φmon : IsInjective φ
    φmon = id
```

Now we prove that the homomorphism whose existence is guaranteed by `FirstHomTheorem` is unique.

```agda
  FirstHomUnique :  {f g : hom (kerquo hh) 𝑩}
    → ( ∀ a →  h a ≈ f .proj₁ ⟨$⟩ (πker hh .proj₁ ⟨$⟩ a) )
    → ( ∀ a →  h a ≈ g .proj₁ ⟨$⟩ (πker hh .proj₁ ⟨$⟩ a) )
    → ∀ [a] → f .proj₁ ⟨$⟩ [a] ≈ g .proj₁ ⟨$⟩ [a]

  FirstHomUnique hfk hgk a = ≈trans (≈sym (hfk a)) (hgk a)
```
