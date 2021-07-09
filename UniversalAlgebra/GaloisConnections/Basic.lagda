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



module _ {ℓ ρ : Level}
         (A : Poset (ℓ ⊔ lsuc ρ) (ℓ ⊔ ρ) (ℓ ⊔ ρ))
         (B : Poset (ℓ ⊔ lsuc ρ) (ℓ ⊔ ρ) (ℓ ⊔ ρ))
         where

 open Poset

 private
  _≤A_ = _≤_ A
  _≤B_ = _≤_ B

 record Galois : Type (ℓ ⊔ lsuc ρ)  where
  field
   F : Carrier A → Carrier B
   G : Carrier B → Carrier A
   GF≥id : ∀ a →  a ≤A G (F a)
   FG≥id : ∀ b →  b ≤B F (G b)

 record Residuation : Type (ℓ ⊔ lsuc ρ)  where
  field
   f     : Carrier A → Carrier B
   fhom  : f Preserves _≤A_ ⟶ _≤B_
   g     : Carrier B → Carrier A
   gf≥id : ∀ a → a ≤A g (f a)
   fg≤id : ∀ b → f (g b) ≤B b



module _ {ℓ : Level}{𝒜 ℬ : Type ℓ} where

 infix 10 _⃗_ _⃖_

 -- For A ⊆ 𝒜, define A ⃗ R = {b : b ∈ ℬ,  ∀ a ∈ A → R a b }
 _⃗_ : (A : Pred 𝒜 ℓ) (R : REL 𝒜 ℬ ℓ) → Pred ℬ ℓ
 A ⃗ R = λ b → (a : 𝒜) → a ∈ A → R a b

 -- For B ⊆ ℬ, define R ⃖ B = {a : a ∈ 𝒜,  ∀ b ∈ B → R a b }
 _⃖_ : (R : REL 𝒜 ℬ ℓ)(B : Pred ℬ ℓ) → Pred 𝒜 ℓ
 R ⃖ B = λ a → (b : ℬ) → b ∈ B → R a b


 ←→≥id : {A : Pred 𝒜 ℓ} {R : REL 𝒜 ℬ ℓ} → A ⊆ R ⃖ (A ⃗ R)
 ←→≥id p b ARb = ARb _ p

 →←≥id : {B : Pred ℬ ℓ} {R : REL 𝒜 ℬ ℓ}  → B ⊆ (R ⃖ B) ⃗ R
 →←≥id p a aRB = aRB _ p

 →←→⊆→ : {A : Pred 𝒜 ℓ}{R : REL 𝒜 ℬ ℓ} → (R ⃖ (A ⃗ R)) ⃗ R ⊆ A ⃗ R
 →←→⊆→ p a Aa = p a (λ b ARb → ARb a Aa)

 ←→←⊆← : {B : Pred ℬ ℓ}{R : REL 𝒜 ℬ ℓ}  → R ⃖ ((R ⃖ B) ⃗ R) ⊆ R ⃖ B
 ←→←⊆← p b Bb = p b (λ a aRB → aRB b Bb)

module _ {ℓ ρ : Level}{𝒜 ℬ : Type ℓ} where


 -- Definition of "closed" with respect to the closure operator λ A → R ⃖ (A ⃗ R)
 ←→Closed : {A : Pred 𝒜 ℓ} {R : REL 𝒜 ℬ ℓ} → Type ℓ
 ←→Closed {A = A}{R} = R ⃖ (A ⃗ R) ⊆ A

 -- Definition of "closed" with respect to the closure operator λ B → (R ⃖ B) ⃗ R
 →←Closed : {B : Pred ℬ ℓ} {R : REL 𝒜 ℬ ℓ} → Type ℓ
 →←Closed {B = B}{R} = (R ⃖ B) ⃗ R ⊆ B

\end{code}


--------------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

