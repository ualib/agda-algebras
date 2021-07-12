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

open import Agda.Primitive          using    ( _⊔_ ;  Level ; lsuc)
                                    renaming ( Set to Type )
open import Relation.Binary.Bundles using    ( Poset )
open import Relation.Binary.Core    using    ( REL ; Rel ; _⇒_ ; _Preserves_⟶_ )
open import Relation.Unary          using    ( _⊆_ ;  _∈_ ; Pred   )



module _ {α β ρ₁ ρ₂ ρ₃ ρ₄ : Level}
         (A : Poset α ρ₁ ρ₂)
         (B : Poset β ρ₃ ρ₄)
         where

 open Poset

 private
  _≤A_ = _≤_ A
  _≤B_ = _≤_ B

 record Galois : Type (lsuc (α ⊔ β ⊔ ρ₂ ⊔ ρ₄))  where
  field
   F : Carrier A → Carrier B
   G : Carrier B → Carrier A
   GF≥id : ∀ a →  a ≤A G (F a)
   FG≥id : ∀ b →  b ≤B F (G b)

module _ {α β : Level}{𝒜 : Type α}{ℬ : Type β} where

 -- For A ⊆ 𝒜, define A ⃗ R = {b : b ∈ ℬ,  ∀ a ∈ A → R a b }
 _⃗_ : ∀ {ρ₁ ρ₂} → Pred 𝒜 ρ₁ → REL 𝒜 ℬ ρ₂ → Pred ℬ (α ⊔ ρ₁ ⊔ ρ₂)
 A ⃗ R = λ b → A ⊆ (λ a → R a b)

 -- For B ⊆ ℬ, define R ⃖ B = {a : a ∈ 𝒜,  ∀ b ∈ B → R a b }
 _⃖_ : ∀ {ρ₁ ρ₂} → REL 𝒜 ℬ ρ₁ → Pred ℬ ρ₂ → Pred 𝒜 (β ⊔ ρ₁ ⊔ ρ₂)
 R ⃖ B = λ a → B ⊆ R a

 ←→≥id : ∀ {ρ₁ ρ₂} {A : Pred 𝒜 ρ₁} {R : REL 𝒜 ℬ ρ₂} → A ⊆ R ⃖ (A ⃗ R)
 ←→≥id p b = b p

 →←≥id : ∀ {ρ₁ ρ₂} {B : Pred ℬ ρ₁} {R : REL 𝒜 ℬ ρ₂}  → B ⊆ (R ⃖ B) ⃗ R
 →←≥id p a = a p

 →←→⊆→ : ∀ {ρ₁ ρ₂} {A : Pred 𝒜 ρ₁}{R : REL 𝒜 ℬ ρ₂} → (R ⃖ (A ⃗ R)) ⃗ R ⊆ A ⃗ R
 →←→⊆→ p a = p (λ z → z a)

 ←→←⊆← : ∀ {ρ₁ ρ₂} {B : Pred ℬ ρ₁}{R : REL 𝒜 ℬ ρ₂}  → R ⃖ ((R ⃖ B) ⃗ R) ⊆ R ⃖ B
 ←→←⊆← p b = p (λ z → z b)

 -- Definition of "closed" with respect to the closure operator λ A → R ⃖ (A ⃗ R)
 ←→Closed : ∀ {ρ₁ ρ₂} {A : Pred 𝒜 ρ₁} {R : REL 𝒜 ℬ ρ₂} → Type _
 ←→Closed {A = A}{R} = R ⃖ (A ⃗ R) ⊆ A

 -- Definition of "closed" with respect to the closure operator λ B → (R ⃖ B) ⃗ R
 →←Closed : ∀ {ρ₁ ρ₂} {B : Pred ℬ ρ₁}{R : REL 𝒜 ℬ ρ₂} → Type _
 →←Closed {B = B}{R} = (R ⃖ B) ⃗ R ⊆ B

\end{code}




--------------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team












-- old, single universe level version
module one-level {ℓ : Level}{𝒜 ℬ : Type ℓ} where

 infix 10 _⃗_ _⃖_

 -- For A ⊆ 𝒜, define A ⃗ R = {b : b ∈ ℬ,  ∀ a ∈ A → R a b }
 _⃗_ : Pred 𝒜 ℓ → REL 𝒜 ℬ ℓ → Pred ℬ ℓ
 A ⃗ R = λ b → A ⊆ (λ a → R a b)

 -- For B ⊆ ℬ, define R ⃖ B = {a : a ∈ 𝒜,  ∀ b ∈ B → R a b }
 _⃖_ : REL 𝒜 ℬ ℓ → Pred ℬ ℓ → Pred 𝒜 ℓ
 R ⃖ B = λ a → B ⊆ R a

 ←→≥id : {A : Pred 𝒜 ℓ} {R : REL 𝒜 ℬ ℓ} → A ⊆ R ⃖ (A ⃗ R)
 ←→≥id p b = b p

 →←≥id : {B : Pred ℬ ℓ} {R : REL 𝒜 ℬ ℓ}  → B ⊆ (R ⃖ B) ⃗ R
 →←≥id p a = a p

 →←→⊆→ : {A : Pred 𝒜 ℓ}{R : REL 𝒜 ℬ ℓ} → (R ⃖ (A ⃗ R)) ⃗ R ⊆ A ⃗ R
 →←→⊆→ p a = p (λ z → z a)

 ←→←⊆← : {B : Pred ℬ ℓ}{R : REL 𝒜 ℬ ℓ}  → R ⃖ ((R ⃖ B) ⃗ R) ⊆ R ⃖ B
 ←→←⊆← p b = p (λ z → z b)
