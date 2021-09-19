---
layout: default
title : "Homomorphisms.Func.Factor module (The Agda Universal Algebra Library)"
date : "2021-09-13"
author: "agda-algebras development team"
---

#### <a id="factoring-homomorphisms-of-setoidalgebra">Factoring Homomorphism of SetoidAlgebras</a>

This is the [Homomorphisms.Func.Factor][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using (𝓞 ; 𝓥 ; Signature )

module Homomorphisms.Func.Factor {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library -------------------------------------------------
open import Data.Product    using ( _,_ ; Σ-syntax )
open import Function        using ( Func ; _∘_ )
open import Level           using ( Level )
open import Relation.Binary using ( Setoid )
open import Relation.Binary.PropositionalEquality as PE using ()
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Unary  using ( _⊆_ )

-- Imports from the Agda Universal Algebra Library ------------------------------------------------
open import Overture.Preliminaries             using ( ∣_∣ ; ∥_∥ )
open import Overture.Func.Preliminaries     using ( _⟶_ )
open import Overture.Inverses         using ( Image_∋_ )
open import Overture.Func.Surjective         using ( IsSurjective ; SurjInvIsInverseʳ ; SurjInv )
open import Relations.Discrete                 using ( kernelRel )
open import Algebras.Setoid.Basic      {𝑆 = 𝑆} using ( 𝕌[_] ; SetoidAlgebra ; _̂_ )
open import Homomorphisms.Func.Basic {𝑆 = 𝑆} using ( hom ; IsHom ; compatible-map )

private variable
 α ρᵃ β ρᵇ γ ρᶜ : Level

\end{code}

If `g : hom 𝑨 𝑩`, `h : hom 𝑨 𝑪`, `h` is surjective, and `ker h ⊆ ker g`, then there exists `φ : hom 𝑪 𝑩` such that `g = φ ∘ h` so the following diagram commutes:

```
𝑨 --- h -->> 𝑪
 \         .
  \       .
   g     φ
    \   .
     \ .
      V
      𝑩
```

We will prove this in case h is both surjective and injective.

\begin{code}

module _ {𝑨 : SetoidAlgebra α ρᵃ}
         (𝑩 : SetoidAlgebra β ρᵇ)
         {𝑪 : SetoidAlgebra γ ρᶜ}
         (gh : hom 𝑨 𝑩)(hh : hom 𝑨 𝑪) where

 open SetoidAlgebra 𝑩 using () renaming (Domain to B )
 open SetoidAlgebra 𝑪 using ( Interp ) renaming (Domain to C )
 open Setoid B using () renaming ( _≈_ to _≈₂_ ; sym to sym₂ )
 open Setoid C using ( trans ) renaming ( _≈_ to _≈₃_ ; sym to sym₃ )
 open SetoidReasoning B
 open Func using ( cong ) renaming (f to _⟨$⟩_ )

 private
  g = _⟨$⟩_ ∣ gh ∣
  hfunc = ∣ hh ∣
  h = _⟨$⟩_ hfunc

 open IsHom
 open Image_∋_

 hom-factor : kernelRel _≈₃_ h ⊆ kernelRel _≈₂_ g → IsSurjective hfunc
              ---------------------------------------------------------
  →           Σ[ φ ∈ hom 𝑪 𝑩 ] ∀ a → (g a) ≈₂ ∣ φ ∣ ⟨$⟩ (h a)

 hom-factor Khg hE = (φmap , φhom) , gφh
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


  φmap : C ⟶ B
  _⟨$⟩_ φmap = g ∘ h⁻¹
  Func.cong φmap = Khg ∘ ζ

  gφh : (a : 𝕌[ 𝑨 ]) → g a ≈₂ φmap ⟨$⟩ (h a)
  gφh a = Khg ξ


  open Func φmap using () renaming (cong to φcong)
  φcomp : compatible-map 𝑪 𝑩 φmap
  φcomp {f}{c} = begin
    φmap ⟨$⟩ ((f ̂ 𝑪) c)   ≈˘⟨ φcong (Func.cong Interp (PE.refl , (λ _ → η))) ⟩
    g (h⁻¹ ((f ̂ 𝑪)(h ∘ (h⁻¹ ∘ c))))   ≈˘⟨ φcong (compatible ∥ hh ∥) ⟩
    g (h⁻¹ (h ((f ̂ 𝑨)(h⁻¹ ∘ c))))   ≈˘⟨ gφh ((f ̂ 𝑨)(h⁻¹ ∘ c)) ⟩
    g ((f ̂ 𝑨)(h⁻¹ ∘ c))    ≈˘⟨ sym₂ (compatible ∥ gh ∥) ⟩
    (f ̂ 𝑩)(g ∘ (h⁻¹ ∘ c)) ∎

  φhom : IsHom 𝑪 𝑩 φmap
  φhom = record { compatible = φcomp
                ; preserves≈ = Func.cong φmap }


\end{code}


--------------------------------

<span style="float:left;">[← Homomorphisms.Func.Kernels](Homomorphisms.Func.Kernels.html)</span>
<span style="float:right;">[Homomorphisms.Func.Isomorphisms →](Homomorphisms.Func.Isomorphisms.html)</span>

{% include UALib.Links.md %}


























