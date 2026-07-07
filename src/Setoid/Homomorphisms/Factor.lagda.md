---
layout: default
title : "Setoid.Homomorphisms.Factor module (The Agda Universal Algebra Library)"
date : "2021-09-13"
author: "agda-algebras development team"
---

#### Factoring Homomorphism of Algebras

This is the [Setoid.Homomorphisms.Factor][] module of the [Agda Universal Algebra Library][].

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Homomorphisms.Factor where

-- Imports from Agda and the Agda Standard Library -------------------------------------------------
open import Data.Product                           using ( _,_ ; proj₁ ; proj₂ ; Σ-syntax )
open import Function     renaming ( Func to _⟶_ )  using ( _∘_ ; _$_ )
open import Level                                  using ( Level )
open import Relation.Binary                        using ( Setoid )
open import Relation.Unary                         using ( _⊆_ )
open import Relation.Binary.PropositionalEquality  using (refl)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ------------------------------------------------
open import Overture                    using  ( kernelRel ; 𝓞 ; 𝓥 ; Signature)
open import Setoid.Functions            using  ( IsSurjective ; SurjInv
                                               ; SurjInvIsInverseʳ ; epic-factor )
open import Setoid.Algebras             using  ( Algebra ; 𝕌[_] ; _^_ ; 𝔻[_] )
open import Setoid.Homomorphisms.Basic  using  ( hom ; IsHom ; compatible-map
                                               ; epi ; IsEpi)

private variable α ρᵃ β ρᵇ γ ρᶜ : Level
```
-->

If `g : hom 𝑨 𝑩`, `h : hom 𝑨 𝑪`, `h` is surjective, and `ker h ⊆ ker g`, then there exists `φ : hom 𝑪 𝑩` such that `g = φ ∘ h` so the following diagram commutes:

    𝑨 --- h -->> 𝑪
     \         .
      \       .
       g     φ
        \   .
         \ .
          V
          𝑩

We will prove this in case h is both surjective and injective.

```agda
module _  {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ} {𝑩 : Algebra β ρᵇ} {𝑪 : Algebra γ ρᶜ}
          ((gfunc , ghom) : hom 𝑨 𝑩)((hfunc , hhom ) : hom 𝑨 𝑪) where

  open Algebra 𝑪      using ( Interp )
  open Setoid 𝔻[ 𝑩 ]  using ()         renaming ( _≈_ to _≈₂_ )
  open Setoid 𝔻[ 𝑪 ]  using ( trans )  renaming ( _≈_ to _≈₃_ ; sym to sym₃ )
  open _⟶_            using ( cong )   renaming ( to to _⟨$⟩_ )

  private
    g = _⟨$⟩_ gfunc
    h = _⟨$⟩_ hfunc

  open IsHom

  HomFactor : kernelRel _≈₃_ h ⊆ kernelRel _≈₂_ g → IsSurjective hfunc
    → Σ[ (φ , _) ∈ hom 𝑪 𝑩 ] ∀ a → g a ≈₂ φ ⟨$⟩ h a

  HomFactor Khg hE = (φ , φhom) , gφh
    where
    kerpres : ∀ a₀ a₁ → h a₀ ≈₃ h a₁ → g a₀ ≈₂ g a₁
    kerpres a₀ a₁ hyp = Khg hyp

    h⁻¹ : 𝕌[ 𝑪 ] → 𝕌[ 𝑨 ]
    h⁻¹ = SurjInv hfunc hE

    η : ∀ {c} → h (h⁻¹ c) ≈₃ c
    η = SurjInvIsInverseʳ hfunc hE

    ξ : ∀ {a} → h a ≈₃ h (h⁻¹ (h a))
    ξ = sym₃ η

    ζ : ∀{x y} → x ≈₃ y → h (h⁻¹ x) ≈₃ h (h⁻¹ y)
    ζ xy = trans η (trans xy (sym₃ η))

    φ : 𝔻[ 𝑪 ] ⟶ 𝔻[ 𝑩 ]
    φ ⟨$⟩ x = (g ∘ h⁻¹) x
    φ .cong = Khg ∘ ζ

    gφh : (a : 𝕌[ 𝑨 ]) → g a ≈₂ φ ⟨$⟩ h a
    gφh _ = Khg ξ

    φcomp : compatible-map 𝑪 𝑩 φ
    φcomp {f}{c} =
      begin
      g (h⁻¹ $ (f ^ 𝑪) c)            ≈˘⟨ φcong (cong Interp (refl , λ _ → SurjInvIsInverseʳ hfunc hE)) ⟩
      g (h⁻¹ $ f ^ 𝑪 $ h ∘ h⁻¹ ∘ c)  ≈˘⟨ φcong (compatible hhom) ⟩
      g (h⁻¹ $ h $ f ^ 𝑨 $ h⁻¹ ∘ c)  ≈˘⟨ gφh $ (f ^ 𝑨) (h⁻¹ ∘ c) ⟩
      g (f ^ 𝑨 $ h⁻¹ ∘ c)            ≈⟨ compatible ghom ⟩
      (f ^ 𝑩)(g ∘ h⁻¹ ∘ c)           ∎
      where
      open SetoidReasoning 𝔻[ 𝑩 ]
      open _⟶_ φ using () renaming (cong to φcong)

    φhom : IsHom 𝑪 𝑩 φ
    φhom .compatible = φcomp
```

If, in addition, `g` is surjective, then so will be the factor `φ`.

```agda
  HomFactorEpi :  kernelRel _≈₃_ h ⊆ kernelRel _≈₂_ g
    → IsSurjective hfunc → IsSurjective gfunc
    → Σ[ (φ , _) ∈ epi 𝑪 𝑩 ] ∀ a → g a ≈₂ φ ⟨$⟩ h a

  HomFactorEpi Khg hE gE = (φmap , φepi) , gφh
    where
    open IsEpi using (isHom; isSurjective)

    homfactor : Σ[ (φ , _) ∈ hom 𝑪 𝑩 ] ∀ a → g a ≈₂ φ ⟨$⟩ h a
    homfactor = HomFactor Khg hE

    φ : hom 𝑪 𝑩
    φ = homfactor .proj₁

    φmap : 𝔻[ 𝑪 ] ⟶ 𝔻[ 𝑩 ]
    φmap = φ .proj₁

    gφh : (a : 𝕌[ 𝑨 ]) → g a ≈₂ φmap ⟨$⟩ (h a)
    gφh = homfactor .proj₂

    φepi : IsEpi 𝑪 𝑩 φmap
    φepi .isHom = φ .proj₂
    φepi .isSurjective = epic-factor gfunc hfunc φmap gE gφh
```
