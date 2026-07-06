---
layout: default
title : "Setoid.Relations.Quotients module (The Agda Universal Algebra Library)"
date : "2021-09-16"
author: "the agda-algebras development team"
---

### Quotients of setoids

This is the [Setoid.Relations.Quotients][] module of the [Agda Universal Algebra Library][].

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Relations.Quotients where

-- Imports from Agda and the Agda Standard Library  -------------------------------
open import Agda.Primitive    using () renaming ( Set to Type )
open import Data.Product      using ( Σ-syntax ) renaming ( _×_ to _∧_ )
open import Function          using ( id ) renaming ( Func to _⟶_ )
open import Level using ( Level ; _⊔_ ; suc )
open import Relation.Binary   using ( IsEquivalence ) renaming ( Rel to BinaryRel )
open import Relation.Unary    using ( Pred ; _∈_ ; _⊆_ )
open import Relation.Binary   using ( Setoid )
open import Relation.Binary.PropositionalEquality as ≡
                              using ( _≡_ )

-- Imports from agda-algebras -----------------------------------------------------
open import Overture                   using ( proj₁ ; proj₂ ; [_] ; Equivalence )
open import Setoid.Relations.Discrete  using ( fker )

private variable α β ρᵃ ρᵇ ℓ : Level
```
-->

#### Kernels

A prominent example of an equivalence relation is the kernel of any function.

```agda
open _⟶_ using ( cong )

module _ {𝐴 : Setoid α ρᵃ}{𝐵 : Setoid β ρᵇ} where
  open Setoid 𝐴  using ( refl ) renaming (Carrier to A )
  open Setoid 𝐵  using ( sym ; trans )

  ker-IsEquivalence : (f : 𝐴 ⟶ 𝐵) → IsEquivalence (fker f)
  IsEquivalence.refl   (ker-IsEquivalence f) = cong f refl
  IsEquivalence.sym    (ker-IsEquivalence f) = sym
  IsEquivalence.trans  (ker-IsEquivalence f) = trans

record IsBlock  {A : Type α}{ρ : Level}
                (P : Pred A ρ){R : BinaryRel A ρ} : Type(α ⊔ suc ρ) where
  constructor mkblk
  field
    a : A
    P≈[a] : ∀ x → (x ∈ P → [ a ]{ρ} R x) ∧ ([ a ]{ρ} R x → x ∈ P)

open IsBlock
```

If `R` is an equivalence relation on `A`, then the *quotient* of `A` modulo `R` is
denoted by `A / R` and is defined to be the collection `{[ u ] ∣  y : A}` of all
`R`-blocks.

```agda
Quotient : (A : Type α) → Equivalence A{ℓ} → Type(α ⊔ suc ℓ)
Quotient A R = Σ[ P ∈ Pred A _ ] IsBlock P {(proj₁ R)}

_/_ : (A : Type α) → Equivalence A{ℓ} → Setoid _ _
A / R = record { Carrier = A ; _≈_ = (proj₁ R) ; isEquivalence = (proj₂ R) }

infix -1 _/_
```

We use the following type to represent an R-block with a designated representative.

```agda
open Setoid
⟪_⟫ : {α : Level}{A : Type α} → A → {R : Equivalence A{ℓ}} → Carrier (A / R)
⟪ a ⟫{R} = a

module _ {A : Type α}{R : Equivalence A{ℓ} } where

  open Setoid (A / R) using () renaming ( _≈_ to _≈₁_ )

  ⟪_∼_⟫-intro : (u v : A) → (proj₁ R) u v → ⟪ u ⟫{R} ≈₁ ⟪ v ⟫{R}
  ⟪ u ∼ v ⟫-intro = id

  ⟪_∼_⟫-elim : (u v : A) → ⟪ u ⟫{R} ≈₁ ⟪ v ⟫{R} → (proj₁ R) u v
  ⟪ u ∼ v ⟫-elim = id

≡→⊆ : {A : Type α}{ρ : Level}(Q R : Pred A ρ) → Q ≡ R → Q ⊆ R
≡→⊆ Q .Q ≡.refl {x} Qx = Qx
```
