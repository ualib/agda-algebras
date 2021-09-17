---
layout: default
title : "Homomorphisms.Setoid.Factor module (The Agda Universal Algebra Library)"
date : "2021-07-17"
author: "agda-algebras development team"
---

#### <a id="factoring-homomorphisms-of-setoidalgebra">Factoring Homomorphism of SetoidAlgebras</a>

This is the [Homomorphisms.Setoid.Factor][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using (𝓞 ; 𝓥 ; Signature )

module Homomorphisms.Setoid.Factor {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library -------------------------------------------------
open import Data.Product    using ( _,_ ; Σ-syntax ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Function        using ( _∘_ ; Func )
open import Function.Equality using ( Π ; _⟶_ )
open import Level           using ( Level )
open import Relation.Binary using ( Setoid )
open import Relation.Binary.PropositionalEquality as PE
                            using ( _≡_ ; cong )
open import Relation.Unary  using ( _⊆_ )

-- -- Imports from the Agda Universal Algebra Library ------------------------------------------------
open import Overture.Preliminaries             using ( ∣_∣ ; ∥_∥ ) renaming (_≈_ to _≐_ )
open import Overture.Setoid.Surjective         using ( IsSurjective ; RightInv ; RightInvIsRightInv ; epic-factor )
-- open import Overture.Setoid.Bijective         using ( IsBijective ; BijInv )
open import Relations.Discrete                 using ( kernel ; kernelRel )
open import Algebras.Setoid.Basic      {𝑆 = 𝑆} using ( 𝕌[_] ; SetoidAlgebra ; _̂_ ; ⟦_⟧ )
open import Homomorphisms.Setoid.Basic {𝑆 = 𝑆} using ( hom ; IsHom ; ≈preserving ; epi )

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
         (g : hom 𝑨 𝑩)(h : hom 𝑨 𝑪) where

 open SetoidAlgebra
 open Setoid
 open Π
 open Func

 private
  A = 𝕌[ 𝑨 ] ; B = 𝕌[ 𝑩 ] ; C = 𝕌[ 𝑪 ]
  _≈A≈_ = _≈_ (Domain 𝑨)
  _≈B≈_ = _≈_ (Domain 𝑩)
  _≈C≈_ = _≈_ (Domain 𝑪)
  hmap = _⟨$⟩_ ∣ h ∣
  gmap = _⟨$⟩_ ∣ g ∣

 open IsHom

 hom-factor : kernelRel _≈C≈_ hmap ⊆ kernelRel _≈B≈_ gmap → IsSurjective ∣ h ∣
              --------------------------------------------------------------------
  →           Σ[ φ ∈ (hom 𝑪 𝑩)] (∀ i → gmap i ≈B≈ ((_⟨$⟩_ ∣ φ ∣) ∘ hmap) i)

 hom-factor Khg hE = (φ , φIsHomCB)  , gφh
  where
  hInv : C → A
  hInv = RightInv ∣ h ∣ hE

  -- ∀ c₀ c₁ → c₀ ≈C≈ c₁ → (hInv c₀) ≈A≈ (hInv c₁)
  hIcong : ≈preserving 𝑪 𝑨 hInv
  hIcong = {!!}

  -- ∀ a₀ a₁ → a₀ ≈A≈ a₁ → (gmap a₀) ≈B≈ (gmap a₁)
  gcong : ≈preserving 𝑨 𝑩 gmap
  gcong = preserves≈ ∥ g ∥

  η : ∀ (c : C) → c ≡ hmap (hInv c)
  η c = PE.sym (RightInvIsRightInv hmap hE c)

  ηη : ∀ f (c : ∥ 𝑆 ∥ f → C) → ∀ i → (c i) ≈C≈ (hmap (hInv (c i)))
  ηη f c i = ≡→≈ 𝑪 (η (c i))

  φ : C → B
  φ = gmap ∘ hInv

  φcong : ≈preserving 𝑪 𝑩 φ
  φcong hyp = gcong (hIcong hyp)

  ξ : ∀ a → kernel hmap (a , hInv (hmap a))
  ξ a = η (hmap a)

  gφh : ∀ b → (gmap b ≈B≈ (φ ∘ hmap) b)
  gφh b = Khg (≡→≈ 𝑪 (ξ b))

  lem0 : ∀ f (c : ∥ 𝑆 ∥ f → C) → ((f ̂ 𝑪) c) ≈C≈ ((f ̂ 𝑪)(hmap ∘(hInv ∘ c)))
  lem0 f c = Func.cong (Interp 𝑪) (PE.refl , (ηη f c))

  lem0' : ∀ f c → ((f ̂ 𝑪)(hmap ∘(hInv ∘ c))) ≈C≈ (hmap((f ̂ 𝑨)(hInv ∘ c)))
  lem0' f c = sym (Domain 𝑪) (compatible ∥ h ∥ f (hInv ∘ c))

  lem1 : ∀ f c → (φ ((f ̂ 𝑪) c)) ≈B≈ (φ ((f ̂ 𝑪)(hmap ∘(hInv ∘ c))))
  lem1 f c = φcong (lem0 f c)

  lem2 : ∀ f c → (φ ((f ̂ 𝑪)(hmap ∘(hInv ∘ c)))) ≈B≈ (φ (hmap((f ̂ 𝑨)(hInv ∘ c))))
  lem2 f c = φcong (lem0' f c)
  lem3 : ∀ f c → (φ (hmap((f ̂ 𝑨)(hInv ∘ c)))) ≈B≈ (gmap((f ̂ 𝑨)(hInv ∘ c)))
  lem3 f c = sym (Domain 𝑩) (gφh ((f ̂ 𝑨)(hInv ∘ c)))
  lem4 : ∀ f c → (gmap((f ̂ 𝑨)(hInv ∘ c))) ≈B≈ ((f ̂ 𝑩)(λ x → gmap(hInv (c x))))
  lem4 f c = compatible ∥ g ∥ f (hInv ∘ c)
  compat : ∀ f c → (φ ((f ̂ 𝑪) c)) ≈B≈ ((f ̂ 𝑩)(φ ∘ c))
  compat f c = trans (Domain 𝑩) (lem1 f c) (trans (Domain 𝑩) (lem2 f c) (trans (Domain 𝑩) (lem3 f c) (lem4 f c)))
  φIsHomCB : IsHom 𝑪 𝑩 φ
  φIsHomCB = record { compatible = compat ; preserves≈ = φcong }
 -- iso-factor : (g : hom 𝑨 𝑩)(h : hom 𝑨 𝑪) → IsSurjective ∣ h ∣
 --  →           SInjective{𝑨 = Domain 𝑨}{Domain 𝑪} ∣ h ∣
 --  →           kernelRel _≈C≈_ ∣ h ∣ ⊆ kernelRel _≈B≈_ ∣ g ∣
 --              --------------------------------------------------------------------
 --  →           Σ[ φ ∈ (hom 𝑪 𝑩)] (∀ i → ∣ g ∣ i ≈B≈ (∣ φ ∣ ∘ ∣ h ∣) i)

 -- iso-factor g h hE hM Khg = (φ , φIsHomCB)  , gφh
 --  where
 --  hInv : C → A
 --  hInv = SurjInv ∣ h ∣ hE

 --  -- ∀ c₀ c₁ → c₀ ≈C≈ c₁ → (hInv c₀) ≈A≈ (hInv c₁)
 --  hIcong : ≈preserving 𝑪 𝑨 hInv
 --  hIcong {x}{y} xy = SInjInvPreserves≈ {𝑨 = Domain 𝑨}{Domain 𝑪} ∣ h ∣ hM (hE x) (hE y) xy

 --  -- ∀ a₀ a₁ → a₀ ≈A≈ a₁ → (∣ g ∣ a₀) ≈B≈ (∣ g ∣ a₁)
 --  gcong : ≈preserving 𝑨 𝑩 ∣ g ∣
 --  gcong = preserves≈ ∥ g ∥

 --  η : ∀ (c : C) → c ≡ ∣ h ∣ (hInv c)
 --  η c = PE.sym (SurjInvIsRightInv ∣ h ∣ hE c)

 --  ηη : ∀ f (c : ∥ 𝑆 ∥ f → C) → ∀ i → (c i) ≈C≈ (∣ h ∣ (hInv (c i)))
 --  ηη f c i = ≡→≈ 𝑪 (η (c i))

 --  φ : C → B
 --  φ = ∣ g ∣ ∘ hInv

 --  φcong : ≈preserving 𝑪 𝑩 φ
 --  φcong hyp = gcong (hIcong hyp)

 --  ξ : ∀ a → kernel ∣ h ∣ (a , hInv (∣ h ∣ a))
 --  ξ a = η (∣ h ∣ a)

 --  gφh : ∀ b → (∣ g ∣ b ≈B≈ (φ ∘ ∣ h ∣) b)
 --  gφh b = Khg (≡→≈ 𝑪 (ξ b))

 --  lem0 : ∀ f (c : ∥ 𝑆 ∥ f → C) → ((f ̂ 𝑪) c) ≈C≈ ((f ̂ 𝑪)(∣ h ∣ ∘(hInv ∘ c)))
 --  lem0 f c = Func.cong (Interp 𝑪) (PE.refl , (ηη f c))

 --  lem0' : ∀ f c → ((f ̂ 𝑪)(∣ h ∣ ∘(hInv ∘ c))) ≈C≈ (∣ h ∣((f ̂ 𝑨)(hInv ∘ c)))
 --  lem0' f c = sym (Domain 𝑪) (compatible ∥ h ∥ f (hInv ∘ c))

 --  lem1 : ∀ f c → (φ ((f ̂ 𝑪) c)) ≈B≈ (φ ((f ̂ 𝑪)(∣ h ∣ ∘(hInv ∘ c))))
 --  lem1 f c = φcong (lem0 f c)

 --  lem2 : ∀ f c → (φ ((f ̂ 𝑪)(∣ h ∣ ∘(hInv ∘ c)))) ≈B≈ (φ (∣ h ∣((f ̂ 𝑨)(hInv ∘ c))))
 --  lem2 f c = φcong (lem0' f c)
 --  lem3 : ∀ f c → (φ (∣ h ∣((f ̂ 𝑨)(hInv ∘ c)))) ≈B≈ (∣ g ∣((f ̂ 𝑨)(hInv ∘ c)))
 --  lem3 f c = sym (Domain 𝑩) (gφh ((f ̂ 𝑨)(hInv ∘ c)))
 --  lem4 : ∀ f c → (∣ g ∣((f ̂ 𝑨)(hInv ∘ c))) ≈B≈ ((f ̂ 𝑩)(λ x → ∣ g ∣(hInv (c x))))
 --  lem4 f c = compatible ∥ g ∥ f (hInv ∘ c)
 --  compat : ∀ f c → (φ ((f ̂ 𝑪) c)) ≈B≈ ((f ̂ 𝑩)(φ ∘ c))
 --  compat f c = trans (Domain 𝑩) (lem1 f c) (trans (Domain 𝑩) (lem2 f c) (trans (Domain 𝑩) (lem3 f c) (lem4 f c)))
 --  φIsHomCB : IsHom 𝑪 𝑩 φ
 --  φIsHomCB = record { compatible = compat ; preserves≈ = φcong }

\end{code}

Here's another version where we work with the standard kernels (instead of the "setoid kernels").

\begin{code}

 -- iso-factor' : (g : hom 𝑨 𝑩)(h : hom 𝑨 𝑪) → IsSurjective ∣ h ∣
 --  →            SInjective{𝑨 = Domain 𝑨}{Domain 𝑪} ∣ h ∣
 --  →            kernel ∣ h ∣ ⊆ kernel ∣ g ∣
 --               --------------------------------------------------------
 --  →            Σ[ φ ∈ (hom 𝑪 𝑩)] (∀ i → ∣ g ∣ i ≈B≈ (∣ φ ∣ ∘ ∣ h ∣) i)

 -- iso-factor' g h hE hM Khg = (φ , φIsHomCB)  , gφh
 --  where
 --  hInv : C → A
 --  hInv = SurjInv ∣ h ∣ hE

 --  -- ∀ c₀ c₁ → c₀ ≈C c₁ → (hInv c₀) ≈A (hInv c₁)
 --  hIcong : ≈preserving 𝑪 𝑨 hInv
 --  hIcong {x}{y} xy = SInjInvPreserves≈ {𝑨 = Domain 𝑨}{Domain 𝑪} ∣ h ∣ hM (hE x) (hE y) xy

 --  -- ∀ a₀ a₁ → a₀ ≈A a₁ → (∣ g ∣ a₀) ≈B (∣ g ∣ a₁)
 --  gcong : ≈preserving 𝑨 𝑩 ∣ g ∣
 --  gcong = preserves≈ ∥ g ∥

 --  η : ∀ (c : C) → c ≡ ∣ h ∣ (hInv c)
 --  η c = PE.sym (SurjInvIsRightInv ∣ h ∣ hE c)

 --  ηη : ∀ f (c : ∥ 𝑆 ∥ f → 𝕌[ 𝑪 ]) → ∀ i → (c i) ≈C≈ (∣ h ∣ (hInv (c i)))
 --  ηη f c i = ≡→≈ 𝑪 (η (c i))

 --  φ : C → B
 --  φ = ∣ g ∣ ∘ hInv

 --  φcong : ≈preserving 𝑪 𝑩 φ
 --  φcong hyp = gcong (hIcong hyp)

 --  ξ : ∀ a → kernel ∣ h ∣ (a , hInv (∣ h ∣ a))
 --  ξ a = η (∣ h ∣ a)

 --  gφh' : ∀ b → (∣ g ∣ b ≡ (φ ∘ ∣ h ∣) b)
 --  gφh' b = Khg (ξ b)

 --  gφh : ∀ b → (∣ g ∣ b ≈B≈ (φ ∘ ∣ h ∣) b)
 --  gφh b = ≡→≈ 𝑩 (gφh' b)

 --  lem0 : ∀ f (c : ∥ 𝑆 ∥ f → 𝕌[ 𝑪 ]) → ((f ̂ 𝑪) c) ≈C≈ ((f ̂ 𝑪)(∣ h ∣ ∘(hInv ∘ c)))
 --  lem0 f c = Func.cong (Interp 𝑪) (PE.refl , (ηη f c))

 --  lem0' : ∀ f c → ((f ̂ 𝑪)(∣ h ∣ ∘(hInv ∘ c))) ≈C≈ (∣ h ∣((f ̂ 𝑨)(hInv ∘ c)))
 --  lem0' f c = sym (Domain 𝑪) (compatible ∥ h ∥ f (hInv ∘ c))

 --  lem1 : ∀ f c → (φ ((f ̂ 𝑪) c)) ≈B≈ (φ ((f ̂ 𝑪)(∣ h ∣ ∘(hInv ∘ c))))
 --  lem1 f c = φcong (lem0 f c)

 --  lem2 : ∀ f c → (φ ((f ̂ 𝑪)(∣ h ∣ ∘(hInv ∘ c)))) ≈B≈ (φ (∣ h ∣((f ̂ 𝑨)(hInv ∘ c))))
 --  lem2 f c = φcong (lem0' f c)
 --  lem3 : ∀ f c → (φ (∣ h ∣((f ̂ 𝑨)(hInv ∘ c)))) ≈B≈ (∣ g ∣((f ̂ 𝑨)(hInv ∘ c)))
 --  lem3 f c = sym (Domain 𝑩) (gφh ((f ̂ 𝑨)(hInv ∘ c)))
 --  lem4 : ∀ f c → (∣ g ∣((f ̂ 𝑨)(hInv ∘ c))) ≈B≈ ((f ̂ 𝑩)(λ x → ∣ g ∣(hInv (c x))))
 --  lem4 f c = compatible ∥ g ∥ f (hInv ∘ c)
 --  compat : ∀ f c → (φ ((f ̂ 𝑪) c)) ≈B≈ ((f ̂ 𝑩)(φ ∘ c))
 --  compat f c = trans (Domain 𝑩) (lem1 f c) (trans (Domain 𝑩) (lem2 f c) (trans (Domain 𝑩) (lem3 f c) (lem4 f c)))
 --  φIsHomCB : IsHom 𝑪 𝑩 φ
 --  φIsHomCB = record { compatible = compat ; preserves≈ = φcong }

\end{code}

If, in addition to the hypotheses of the last theorem, we assume g is epic, then so is φ. (Note that the proof also requires an additional local function extensionality postulate, `funext β β`.)

\begin{code}

 -- iso-factor-epi : (g : hom 𝑨 𝑩)(h : hom 𝑨 𝑪) → IsSurjective ∣ h ∣
 --  →               SInjective{𝑨 = Domain 𝑨}{Domain 𝑪} ∣ h ∣
 --  →               IsSurjective ∣ g ∣
 --  →               kernel ∣ h ∣ ⊆ kernel ∣ g ∣
 --                  ---------------------------------------------
 --  →               Σ[ φ ∈ epi{𝑨 = 𝑪}{𝑩} ] (∀ i → ∣ g ∣ i ≈B≈ (∣ φ ∣ ∘ ∣ h ∣) i)

 -- iso-factor-epi g h hE hM gE Khg = (fst ∣ φF ∣ , record { isHom = snd ∣ φF ∣
 --                                                        ; isSurjective = φE }) , ∥ φF ∥
 --  where
 --   φF : Σ[ φ ∈ hom 𝑪 𝑩 ] (∀ i → ∣ g ∣ i ≈B≈ (∣ φ ∣ ∘ ∣ h ∣) i)
 --   φF = iso-factor' g h hE hM Khg

 --   φ : C → B
 --   φ = ∣ g ∣ ∘ (SurjInv ∣ h ∣ hE)

 --   φE : IsSurjective φ
 --   φE = epic-factor ∣ g ∣ ∣ h ∣ φ {!!} gE -- epic-factor  ∣ g ∣ ∣ h ∣ φ gE


-- epic-factor : {C : Type γ}(f : A → B)(g : A → C)(h : C → B)
 --  →            f ≈ h ∘ g → IsSurjective f → IsSurjective h

\end{code}

--------------------------------

<span style="float:left;">[← Homomorphisms.Setoid.Kernels](Homomorphisms.Setoid.Kernels.html)</span>
<span style="float:right;">[Homomorphisms.Setoid.Isomorphisms →](Homomorphisms.Setoid.Isomorphisms.html)</span>

{% include UALib.Links.md %}



























