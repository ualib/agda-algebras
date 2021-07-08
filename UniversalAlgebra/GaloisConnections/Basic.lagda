---
layout: default
title : GaloisConnections.Basic module (The Agda Universal Algebra Library)
date : 2021-07-01
author: [agda-algebras development team][]
---

## Galois Connection

If 𝑨 = (A, ≤) and 𝑩 = (B, ≤) are two partially ordered sets (posets), then a
*Galois connection* between 𝑨 and 𝑩 is a pair (F , G) of functions such that

1. F : A → B
2. G : B → A
3. ∀ (a : A)(b : B)  →  F(a) ≤   b   →    a  ≤ G(b)
r. ∀ (a : A)(b : B)  →    a  ≤ G(b)  →  F(a) ≤   b

In other terms, F is a left adjoint of G and G is a right adjoint of F.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module GaloisConnections.Basic where

open import Agda.Primitive          using    ( _⊔_ ;  Level )
                                    renaming ( Set to Type )
open import Relation.Binary.Bundles using    ( Poset )
open import Relation.Binary.Core    using    ( REL ; Rel ; _⇒_ )
open import Relation.Unary          using    ( _⊆_ ;  _∈_ ; Pred   )

module _ {α α₁ α₂ : Level}(A : Poset α α₁ α₂)
         {β β₁ β₂ : Level}(B : Poset β β₁ β₂)
         where

 open Poset

 private
  _≤A_ = _≤_ A
  _≤B_ = _≤_ B

 record Galois : Type  (α ⊔ α₂ ⊔ β ⊔ β₂) where
  field
   F : Carrier A → Carrier B
   G : Carrier B → Carrier A
   F⊣G : ∀ a b → (F a) ≤B b → a ≤A (G b)
   F⊢G : ∀ a b → a ≤A (G b) → (F a) ≤B b


private variable ℓ ρ : Level


module _ {𝒜 ℬ : Type ℓ} where

 -- For A ⊆ 𝒜, define A ⃗ R = {b : b ∈ ℬ,  ∀ a ∈ A → R a b }
 _⃗_ : (A : Pred 𝒜 (ℓ ⊔ ρ)) (R : REL 𝒜 ℬ ρ) → Pred ℬ (ℓ  ⊔ ρ)
 A ⃗ R = λ b → (a : 𝒜) → a ∈ A → R a b

 -- For B ⊆ ℬ, define R ⃖ B = {a : a ∈ 𝒜,  ∀ b ∈ B → R a b }
 _⃖_ : (R : REL 𝒜 ℬ ρ)(B : Pred ℬ (ℓ ⊔ ρ)) → Pred 𝒜 (ℓ  ⊔ ρ)
 R ⃖ B = λ a → (b : ℬ) → b ∈ B → R a b

 Gal→← : {A : Pred 𝒜 (ℓ ⊔ ρ)} {R : REL 𝒜 ℬ ρ} → A ⊆ R ⃖ (A ⃗ R)
 Gal→← p b ARb = ARb _ p

 Gal←→ : {B : Pred ℬ (ℓ ⊔ ρ)} {R : REL 𝒜 ℬ ρ}  → B ⊆ (R ⃖ B) ⃗ R
 Gal←→ p a aRB = aRB _ p

 Gal→←→ : {A : Pred 𝒜 (ℓ ⊔ ρ)}{R : REL 𝒜 ℬ ρ} → (R ⃖ (A ⃗ R)) ⃗ R ⊆ A ⃗ R
 Gal→←→ p a Aa = p a (λ b ARb → ARb a Aa)

 Gal←→← : {B : Pred ℬ (ℓ ⊔ ρ)}{R : REL 𝒜 ℬ ρ}  → R ⃖ ((R ⃖ B) ⃗ R) ⊆ R ⃖ B
 Gal←→← p b Bb = p b (λ a aRB → aRB b Bb)

module _ {𝒜 ℬ : Type ℓ} where

 Closed→← : {A : Pred 𝒜 (ℓ ⊔ ρ)} {R : REL 𝒜 ℬ ρ} → Type (ℓ ⊔ ρ)
 Closed→← {A = A}{R} = R ⃖ (A ⃗ R) ⊆ A

 Closed←→ : {B : Pred ℬ (ℓ ⊔ ρ)} {R : REL 𝒜 ℬ ρ} → Type (ℓ ⊔ ρ)
 Closed←→ {B = B}{R} = (R ⃖ B) ⃗ R ⊆ B


\end{code}


--------------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

