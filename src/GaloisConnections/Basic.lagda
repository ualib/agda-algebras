---
layout: default
title : "GaloisConnections.Basic module (The Agda Universal Algebra Library)"
date : "2021-07-01"
author: "agda-algebras development team"
---

### <a id="basic-definitions">Basic definitions</a>

This is the [GaloisConnections.Basic][] module of the [Agda Universal Algebra Library][].

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

-- imports from Agda and the Agda Standard Library --------------------------------------
open import Agda.Primitive          using ( _⊔_ ;  Level ; lsuc) renaming ( Set to Type )
open import Relation.Binary.Bundles using ( Poset )
open import Relation.Binary.Core    using ( REL ; Rel ; _⇒_ ; _Preserves_⟶_ )
open import Relation.Unary          using ( _⊆_ ;  _∈_ ; Pred   )


module _ {α β ℓᵃ ρᵃ ℓᵇ ρᵇ : Level}
         (A : Poset α ℓᵃ ρᵃ)
         (B : Poset β ℓᵇ ρᵇ)
         where

 open Poset

 private
  _≤A_ = _≤_ A
  _≤B_ = _≤_ B

 record Galois : Type (lsuc (α ⊔ β ⊔ ρᵃ ⊔ ρᵇ))  where
  field
   F : Carrier A → Carrier B
   G : Carrier B → Carrier A
   GF≥id : ∀ a →  a ≤A G (F a)
   FG≥id : ∀ b →  b ≤B F (G b)


module _ {α β : Level}{𝒜 : Type α}{ℬ : Type β} where

 -- For A ⊆ 𝒜, define A ⃗ R = {b : b ∈ ℬ,  ∀ a ∈ A → R a b }
 _⃗_ : ∀ {ρᵃ ρᵇ} → Pred 𝒜 ρᵃ → REL 𝒜 ℬ ρᵇ → Pred ℬ (α ⊔ ρᵃ ⊔ ρᵇ)
 A ⃗ R = λ b → A ⊆ (λ a → R a b)

 -- For B ⊆ ℬ, define R ⃖ B = {a : a ∈ 𝒜,  ∀ b ∈ B → R a b }
 _⃖_ : ∀ {ρᵃ ρᵇ} → REL 𝒜 ℬ ρᵃ → Pred ℬ ρᵇ → Pred 𝒜 (β ⊔ ρᵃ ⊔ ρᵇ)
 R ⃖ B = λ a → B ⊆ R a

 ←→≥id : ∀ {ρᵃ ρʳ} {A : Pred 𝒜 ρᵃ} {R : REL 𝒜 ℬ ρʳ} → A ⊆ R ⃖ (A ⃗ R)
 ←→≥id p b = b p

 →←≥id : ∀ {ρᵇ ρʳ} {B : Pred ℬ ρᵇ} {R : REL 𝒜 ℬ ρʳ}  → B ⊆ (R ⃖ B) ⃗ R
 →←≥id p a = a p

 →←→⊆→ : ∀ {ρᵃ ρʳ} {A : Pred 𝒜 ρᵃ}{R : REL 𝒜 ℬ ρʳ} → (R ⃖ (A ⃗ R)) ⃗ R ⊆ A ⃗ R
 →←→⊆→ p a = p (λ z → z a)

 ←→←⊆← : ∀ {ρᵇ ρʳ} {B : Pred ℬ ρᵇ}{R : REL 𝒜 ℬ ρʳ}  → R ⃖ ((R ⃖ B) ⃗ R) ⊆ R ⃖ B
 ←→←⊆← p b = p (λ z → z b)

 -- Definition of "closed" with respect to the closure operator λ A → R ⃖ (A ⃗ R)
 ←→Closed : ∀ {ρᵃ ρʳ} {A : Pred 𝒜 ρᵃ} {R : REL 𝒜 ℬ ρʳ} → Type _
 ←→Closed {A = A}{R} = R ⃖ (A ⃗ R) ⊆ A

 -- Definition of "closed" with respect to the closure operator λ B → (R ⃖ B) ⃗ R
 →←Closed : ∀ {ρᵇ ρʳ} {B : Pred ℬ ρᵇ}{R : REL 𝒜 ℬ ρʳ} → Type _
 →←Closed {B = B}{R} = (R ⃖ B) ⃗ R ⊆ B

\end{code}


--------------------------------------

<span style="float:left;">[↑ GaloisConnections](GaloisConnections.html)</span>
<span style="float:right;">[GaloisConnections.Properties →](GaloisConnections.Properties.html)</span>

{% include UALib.Links.md %}

