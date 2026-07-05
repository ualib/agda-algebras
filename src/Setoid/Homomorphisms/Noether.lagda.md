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

module Setoid.Homomorphisms.Noether where

-- Imports from Agda and the Agda Standard Library ---------------------------
open import Data.Product     using (Σ-syntax ; _,_ )  renaming ( _×_ to _∧_)
open import Function         using ( id )             renaming ( Func to _⟶_ )
open import Level            using ( Level )
open import Relation.Binary  using ( Setoid )

open import Relation.Binary.PropositionalEquality as ≡ using ( _≡_ )


-- Imports from agda-algebras ------------------------------------------------
open import Overture                      using ( proj₁ ; proj₂ ; 𝓞 ; 𝓥 ; Signature)
open import Setoid.Algebras               using ( Algebra )
open import Setoid.Functions              using ( IsInjective )
open import Setoid.Homomorphisms.Basic    using ( hom ; IsHom )
open import Setoid.Homomorphisms.Kernels  using ( kerquo ; πker )

private variable α ρᵃ β ρᵇ γ ρᶜ ι : Level
```


#### The First Homomorphism Theorem for setoid algebras


```agda
open _⟶_ using ( cong ) renaming ( to to _⟨$⟩_ )

module _  {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ}{𝑩 : Algebra β ρᵇ}(hh : hom 𝑨 𝑩) where
 open Algebra 𝑩 using ( Interp ) renaming ( Domain to B )
 open Setoid B using ( _≈_ ; refl ; sym ; trans ) -- renaming ( _≈_ to _≈₂_ )
 open Algebra (kerquo hh) using () renaming ( Domain to A/hKer )

 open IsHom
 private
  hfunc = (proj₁ hh)
  h = _⟨$⟩_ hfunc

 FirstHomTheorem :  Σ[ φ ∈ hom (kerquo hh) 𝑩  ]
                    ( ∀ a → h a ≈ (proj₁ φ) ⟨$⟩ ((proj₁ (πker hh)) ⟨$⟩ a) )
                     ∧ IsInjective (proj₁ φ)

 FirstHomTheorem = (φ , φhom) , (λ _ → refl) , φmon
  where
  φ : A/hKer ⟶ B
  _⟨$⟩_ φ = h
  cong φ = id

  φhom : IsHom (kerquo hh) 𝑩 φ
  compatible φhom = trans (compatible (proj₂ hh)) (cong Interp (≡.refl , (λ _ → refl)))

  φmon : IsInjective φ
  φmon = id
```


Now we prove that the homomorphism whose existence is guaranteed by `FirstHomTheorem` is unique.


```agda
 FirstHomUnique :  (f g : hom (kerquo hh) 𝑩)
  →                ( ∀ a →  h a ≈ (proj₁ f) ⟨$⟩ ((proj₁ (πker hh)) ⟨$⟩ a) )
  →                ( ∀ a →  h a ≈ (proj₁ g) ⟨$⟩ ((proj₁ (πker hh)) ⟨$⟩ a) )
  →                ∀ [a]  →  (proj₁ f) ⟨$⟩ [a] ≈ (proj₁ g) ⟨$⟩ [a]

 FirstHomUnique fh gh hfk hgk a = trans (sym (hfk a)) (hgk a)
```
