---
layout: default
title : "Setoid.Algebras.Basic module (Agda Universal Algebra Library)"
date : "2021-04-23"
author: "agda-algebras development team"
---

#### <a id="basic-definitions">Basic definitions for algebras over setoids</a>

This is the [Setoid.Algebras.Basic][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Base.Algebras.Basic using (𝓞 ; 𝓥 ; Signature )

module Setoid.Algebras.Basic {𝑆 : Signature 𝓞 𝓥} where

-- Imports from the Agda and the Agda Standard Library --------------------
open import Agda.Primitive   using ( _⊔_ ; lsuc ) renaming ( Set to Type )
open import Data.Product     using ( _,_ ; _×_ ; Σ-syntax )
open import Function         using ( _∘_ )
open import Function.Bundles using ( Func )
open import Level            using ( Level )
open import Relation.Binary  using ( Setoid ; IsEquivalence )
open import Relation.Binary.PropositionalEquality as ≡
                             using ( _≡_ ; refl )

-- Imports from the Agda Universal Algebra Library ----------------------
open import Base.Overture.Preliminaries using ( ∥_∥ ; ∣_∣ )

private variable
 α ρ ι : Level

ov : Level → Level
ov α = 𝓞 ⊔ 𝓥 ⊔ lsuc α
\end{code}


#### <a id="setoid-algebras">Setoid Algebras</a>

Here we define algebras over a setoid, instead of a mere type with no equivalence on it.

(This approach is inspired by the one taken, e.g., by Andreas Abel in his formalization Birkhoff's completeness theorem; a [pdf is available here](http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf).)

First we define an operator that translates an ordinary signature into a signature over a setoid domain.

\begin{code}

open Setoid using    (_≈_ ; Carrier )
            renaming ( refl  to reflS
                     ; sym   to symS
                     ; trans to transS
                     ; isEquivalence to isEqv )
open Func renaming   ( f to _⟨$⟩_ ; cong to ≈cong )


EqArgs : {𝑆 : Signature 𝓞 𝓥}{ξ : Setoid α ρ}
 →       ∀ {f g} → f ≡ g → (∥ 𝑆 ∥ f → Carrier ξ) → (∥ 𝑆 ∥ g → Carrier ξ) → Type (𝓥 ⊔ ρ)
EqArgs {ξ = ξ} refl u v = ∀ i → (_≈_ ξ) (u i) (v i)



⟨_⟩ : Signature 𝓞 𝓥 → Setoid α ρ → Setoid _ _

Carrier (⟨ 𝑆 ⟩ ξ) = Σ[ f ∈ ∣ 𝑆 ∣ ] ((∥ 𝑆 ∥ f) → ξ .Carrier)
_≈_ (⟨ 𝑆 ⟩ ξ) (f , u) (g , v) = Σ[ eqv ∈ f ≡ g ] EqArgs{ξ = ξ} eqv u v

IsEquivalence.refl  (isEqv (⟨ 𝑆 ⟩ ξ))                     = refl , λ _ → reflS  ξ
IsEquivalence.sym   (isEqv (⟨ 𝑆 ⟩ ξ))(refl , g)           = refl , λ i → symS   ξ (g i)
IsEquivalence.trans (isEqv (⟨ 𝑆 ⟩ ξ))(refl , g)(refl , h) = refl , λ i → transS ξ (g i) (h i)

\end{code}


A setoid algebra is just like an algebra but we require that all basic operations
of the algebra respect the underlying setoid equality. The `Func` record packs a
function (f, aka apply, aka _⟨$⟩_) with a proof (cong) that the function respects
equality.

\begin{code}

record Algebra α ρ : Type (𝓞 ⊔ 𝓥 ⊔ lsuc (α ⊔ ρ)) where
 field
  Domain : Setoid α ρ
  Interp : Func (⟨ 𝑆 ⟩ Domain) Domain
   --      ^^^^^^^^^^^^^^^^^^^^^^^ is a record type with two fields:
   --       1. a function  f : Carrier (⟨ 𝑆 ⟩ Domain)  → Carrier Domain
   --       2. a proof cong : f Preserves _≈₁_ ⟶ _≈₂_ (that f preserves the setoid equalities)
 -- Actually, we already have the following: (it's called "reflexive"; see Structures.IsEquivalence)
 ≡→≈ : ∀{x}{y} → x ≡ y → (_≈_ Domain) x y
 ≡→≈ refl = Setoid.refl Domain

\end{code}

It should be clear that the two types `Algebroid` and `Algebra` are equivalent. (We tend to use the latter throughout most of the [agda-algebras][] library.)

\begin{code}

open Algebra

-- Forgetful Functor
𝕌[_] : Algebra α ρ →  Type α
𝕌[ 𝑨 ] = Carrier (Domain 𝑨)

𝔻[_] : Algebra α ρ →  Setoid α ρ
𝔻[ 𝑨 ] = Domain 𝑨

-- The universe level of a Algebra

Level-of-Alg : {α ρ 𝓞 𝓥 : Level}{𝑆 : Signature 𝓞 𝓥} → Algebra α ρ → Level
Level-of-Alg {α = α}{ρ}{𝓞}{𝓥} _ = 𝓞 ⊔ 𝓥 ⊔ lsuc (α ⊔ ρ)

Level-of-Carrier : {α ρ 𝓞 𝓥  : Level}{𝑆 : Signature 𝓞 𝓥} → Algebra α ρ → Level
Level-of-Carrier {α = α} _ = α


open Algebra

_̂_ : (f : ∣ 𝑆 ∣)(𝑨 : Algebra α ρ) → (∥ 𝑆 ∥ f  →  𝕌[ 𝑨 ]) → 𝕌[ 𝑨 ]

f ̂ 𝑨 = λ a → (Interp 𝑨) ⟨$⟩ (f , a)

\end{code}


#### <a id="level-lifting-setoid-algebra-types">Level lifting setoid algebra types</a>

\begin{code}

module _ (𝑨 : Algebra α ρ) where

 open Algebra 𝑨 using ( Interp ) renaming ( Domain to A )
 open Setoid A using (sym ; trans ) renaming ( Carrier to ∣A∣ ; _≈_ to _≈₁_ ; refl to refl₁ )

 open Level


 Lift-Algˡ : (ℓ : Level) → Algebra (α ⊔ ℓ) ρ

 Domain (Lift-Algˡ ℓ) = record { Carrier = Lift ℓ ∣A∣
                                  ; _≈_ = λ x y → lower x ≈₁ lower y
                                  ; isEquivalence = record { refl = refl₁
                                                           ; sym = sym
                                                           ; trans = trans
                                                           }
                                  }

 Interp (Lift-Algˡ ℓ) ⟨$⟩ (f , la) = lift ((f ̂ 𝑨) (lower ∘ la))
 ≈cong (Interp (Lift-Algˡ ℓ)) (refl , la=lb) = ≈cong (Interp 𝑨) ((refl , la=lb))


 Lift-Algʳ : (ℓ : Level) → Algebra α (ρ ⊔ ℓ)

 Domain (Lift-Algʳ ℓ) =
  record { Carrier = ∣A∣
         ; _≈_ = λ x y → Lift ℓ (x ≈₁ y)
         ; isEquivalence = record { refl = lift refl₁
                                  ; sym = λ x → lift (sym (lower x))
                                  ; trans = λ x y → lift (trans (lower x) (lower y))  }
                                  }

 Interp (Lift-Algʳ ℓ ) ⟨$⟩ (f , la) = (f ̂ 𝑨) la
 ≈cong (Interp (Lift-Algʳ ℓ)) (refl , la≡lb) = lift (≈cong (Interp 𝑨) (≡.refl , λ i → lower (la≡lb i)))

Lift-Alg : (𝑨 : Algebra α ρ)(ℓ₀ ℓ₁ : Level) → Algebra (α ⊔ ℓ₀) (ρ ⊔ ℓ₁)
Lift-Alg 𝑨 ℓ₀ ℓ₁ = Lift-Algʳ (Lift-Algˡ 𝑨 ℓ₀) ℓ₁

\end{code}


--------------------------------

<span style="float:left;">[↑ Setoid.Algebras](Setoid.Algebras.html)</span>
<span style="float:right;">[Setoid.Algebras.Products →](Setoid.Algebras.Products.html)</span>

{% include UALib.Links.md %}
