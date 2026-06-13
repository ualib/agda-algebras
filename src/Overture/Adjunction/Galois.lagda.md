---
layout: default
title : "Overture.Adjunction.Galois module (The Agda Universal Algebra Library)"
date : "2026-05-09"
author: "the agda-algebras development team"
---

### Galois Connections

This is the [Overture.Adjunction.Galois][] module of the [Agda Universal Algebra Library][].


```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Overture.Adjunction.Galois where

-- Imports from Agda and the Agda Standard Library --------------------------------------
open import Agda.Primitive           using () renaming ( Set to Type )
open import Data.Product             using ( _,_ ; _×_ ; swap ; proj₁ )
open import Function.Base            using ( _∘_ ; id )
open import Level                    using ( _⊔_ ;  Level ; suc )
open import Relation.Binary.Bundles  using ( Poset )
open import Relation.Binary.Core     using ( REL ; Rel ; _⇒_ ; _Preserves_⟶_ )
open import Relation.Unary           using ( _⊆_ ;  _∈_ ; Pred   )

open import Relation.Binary.Structures using (IsEquivalence)

private variable α β ℓᵃ ρᵃ ℓᵇ ρᵇ : Level
```


If `𝑨 = (A, ≤)` and `𝑩 = (B, ≤)` are two partially ordered sets (posets), then a
*Galois connection* between `𝑨` and `𝑩` is a pair `(F , G)` of functions such that

1. `F : A → B`
2. `G : B → A`
3. `∀ (a : A)(b : B)  →  F(a)  ≤  b     →  a     ≤  G(b)`
4. `∀ (a : A)(b : B)  →  a     ≤  G(b)  →  F(a)  ≤  b`

In other terms, `F` is a *left adjoint* of `G` and `G` is a *right adjoint* of `F`.


```agda
module _ (𝑨 : Poset α ℓᵃ ρᵃ)(𝑩 : Poset β ℓᵇ ρᵇ) where
 open Poset 𝑨 renaming ( Carrier to A ; _≤_ to _≤ᴬ_ ) using ()
 open Poset 𝑩 renaming ( Carrier to B ; _≤_ to _≤ᴮ_ ) using ()
 record Galois : Type (suc (α ⊔ β ⊔ ρᵃ ⊔ ρᵇ))  where
  field
   F : A → B
   G : B → A
   GF≥id : ∀ a →  a ≤ᴬ G (F a)
   FG≥id : ∀ b →  b ≤ᴮ F (G b)


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
```

#### The poset of subsets of a set

Here we define a type that represents the poset of subsets of a given set equipped
with the usual set inclusion relation.  (It seems there is no definition in the
standard library of this important example of a poset; we should propose adding it.)

```agda
module _ {α ρ : Level} {𝒜 : Type α} where

 _≐_ : Pred 𝒜 ρ → Pred 𝒜 ρ → Type (α ⊔ ρ)
 P ≐ Q = (P ⊆ Q) × (Q ⊆ P)

 open IsEquivalence -- renaming (refl to ref ; sym to symm ; trans to tran)

 ≐-iseqv : IsEquivalence _≐_
 refl ≐-iseqv = id , id
 sym ≐-iseqv = swap
 trans ≐-iseqv (u₁ , u₂) (v₁ , v₂) = v₁ ∘ u₁ , u₂ ∘ v₂

module _ {α : Level} (ρ : Level) (𝒜 : Type α) where
  open Poset using (Carrier; _≈_ ; _≤_; isPartialOrder)


  PosetOfSubsets : Poset (α ⊔ suc ρ) (α ⊔ ρ) (α ⊔ ρ)
  Carrier PosetOfSubsets = Pred 𝒜 ρ
  _≈_ PosetOfSubsets = _≐_
  _≤_ PosetOfSubsets = _⊆_
  isPartialOrder PosetOfSubsets =
    record
      { isPreorder = record  { isEquivalence = ≐-iseqv
                             ; reflexive = proj₁
                             ; trans = λ u v → v ∘ u
                             }
      ; antisym = _,_ }
```

A binary relation from one poset to another induces a Galois connection.  This is
akin to the situation with Adjunctions in Category Theory (unsurprisingly).  In other
words, there is likely a unit/counit definition that is more level polymorphic.

```agda
module _ {ℓ : Level}{𝒜 : Type ℓ} {ℬ : Type ℓ} where

  𝒫𝒜 𝒫ℬ : Poset (suc ℓ) ℓ ℓ
  𝒫𝒜 = PosetOfSubsets ℓ 𝒜
  𝒫ℬ = PosetOfSubsets ℓ ℬ

  -- Every binary relation from one poset to another induces a Galois connection.
  Rel→Gal : (R : REL 𝒜 ℬ ℓ) → Galois 𝒫𝒜 𝒫ℬ
  Rel→Gal R = record  { F = _⃗ R
                      ; G = R ⃖_
                      ; GF≥id = λ _ → ←→≥id
                      ; FG≥id = λ _ → →←≥id }
```

--------------------

<span style="float:left;">[← Overture.Adjunction.Closure](Overture.Adjunction.Closure.html)</span>
<span style="float:right;">[Overture.Adjunction.Residuation →](Overture.Adjunction.Residuation.html)</span>

{% include UALib.Links.md %}
