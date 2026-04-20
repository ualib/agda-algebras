---
layout: default
title : "Base.Adjunction.Galois module (The Agda Universal Algebra Library)"
date : "2021-08-30"
author: "agda-algebras development team"
---

### <a id="Galois connections">Galois Connections</a>

This is the [Base.Adjunction.Galois][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Base.Adjunction.Galois where

-- Imports from Agda and the Agda Standard Library --------------------------------------
open import Agda.Primitive           using () renaming ( Set to Type )
open import Data.Product             using ( _,_ ; _×_ ; swap ) renaming ( proj₁ to fst )
open import Function.Base            using ( _∘_ ; id )
open import Level                    using ( _⊔_ ;  Level ; suc )
open import Relation.Binary.Bundles  using ( Poset )
open import Relation.Binary.Core     using ( REL ; Rel ; _⇒_ ; _Preserves_⟶_ )
open import Relation.Unary           using ( _⊆_ ;  _∈_ ; Pred   )

import Relation.Binary.Structures as BS

private variable α β ℓᵃ ρᵃ ℓᵇ ρᵇ : Level

\end{code}

If `𝑨 = (A, ≤)` and `𝑩 = (B, ≤)` are two partially ordered sets (posets), then a
*Galois connection* between `𝑨` and `𝑩` is a pair `(F , G)` of functions such that

1. `F : A → B`
2. `G : B → A`
3. `∀ (a : A)(b : B)  →  F(a) ≤   b   →    a  ≤ G(b)`
r. `∀ (a : A)(b : B)  →    a  ≤ G(b)  →  F(a) ≤   b`

In other terms, `F` is a *left adjoint* of `G` and `G` is a *right adjoint* of `F`.

\begin{code}

module _ (A : Poset α ℓᵃ ρᵃ)(B : Poset β ℓᵇ ρᵇ) where
 open Poset
 private
  _≤A_ = _≤_ A
  _≤B_ = _≤_ B

 record Galois : Type (suc (α ⊔ β ⊔ ρᵃ ⊔ ρᵇ))  where
  field
   F : Carrier A → Carrier B
   G : Carrier B → Carrier A
   GF≥id : ∀ a →  a ≤A G (F a)
   FG≥id : ∀ b →  b ≤B F (G b)


module _ {𝒜 : Type α}{ℬ : Type β} where

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


#### <a id="the-poset-of-subsets-of-a-set">The poset of subsets of a set</a>

Here we define a type that represents the poset of subsets of a given set equipped with the usual set inclusion relation. (It seems there is no definition in the standard library of this important example of a poset; we should propose adding it.)

\begin{code}
open Poset

module _ {α ρ : Level} {𝒜 : Type α} where

 _≐_ : Pred 𝒜 ρ → Pred 𝒜 ρ → Type (α ⊔ ρ)
 P ≐ Q = (P ⊆ Q) × (Q ⊆ P)

 open BS.IsEquivalence renaming (refl to ref ; sym to symm ; trans to tran)

 ≐-iseqv : BS.IsEquivalence _≐_
 ref ≐-iseqv = id , id
 symm ≐-iseqv = swap
 tran ≐-iseqv (u₁ , u₂) (v₁ , v₂) = v₁ ∘ u₁ , u₂ ∘ v₂


module _ {α : Level} (ρ : Level) (𝒜 : Type α) where

 PosetOfSubsets : Poset (α ⊔ suc ρ) (α ⊔ ρ) (α ⊔ ρ)
 Carrier PosetOfSubsets = Pred 𝒜 ρ
 _≈_ PosetOfSubsets = _≐_
 _≤_ PosetOfSubsets = _⊆_
 isPartialOrder PosetOfSubsets =
  record  { isPreorder = record  { isEquivalence = ≐-iseqv
                                 ; reflexive = fst
                                 ; trans = λ u v → v ∘ u
                                 }
          ; antisym = _,_
          }

\end{code}

A Binary relation from one poset to another induces a Galois connection, but only in a very special
situation, namely when all the involved sets are of the same size.  This is akin to the situation
with Adjunctions in Category Theory (unsurprisingly). In other words, there is likely a
unit/counit definition that is more level polymorphic.

\begin{code}

module _ {ℓ : Level}{𝒜 : Type ℓ} {ℬ : Type ℓ} where

 𝒫𝒜 : Poset (suc ℓ) ℓ ℓ
 𝒫ℬ : Poset (suc ℓ) ℓ ℓ
 𝒫𝒜 = PosetOfSubsets ℓ 𝒜
 𝒫ℬ = PosetOfSubsets ℓ ℬ

 -- Every binary relation from one poset to another induces a Galois connection.
 Rel→Gal : (R : REL 𝒜 ℬ ℓ) → Galois 𝒫𝒜 𝒫ℬ
 Rel→Gal R = record  { F = _⃗ R
                     ; G = R ⃖_
                     ; GF≥id = λ _ → ←→≥id
                     ; FG≥id = λ _ → →←≥id }
\end{code}

--------------------

<span style="float:left;">[← Base.Adjunction.Closure ](Base.Adjunction.Closure.html)</span>
<span style="float:right;">[Base.Adjunction.Residuation →](Base.Adjunction.Residuation.html)</span>

{% include UALib.Links.md %}

