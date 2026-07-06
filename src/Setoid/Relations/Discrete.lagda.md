---
layout: default
title : "Setoid.Relations.Discrete module (The Agda Universal Algebra Library)"
date : "2021-09-16"
author: "the agda-algebras development team"
---

### Discrete Relations on Setoids

This is the [Setoid.Relations.Discrete][] module of the [Agda Universal Algebra Library][].

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Relations.Discrete where

-- Imports from Agda and the Agda Standard Library ----------------------------------------------
open import Agda.Primitive               using () renaming ( Set to Type )
open import Data.Product                 using ( _,_ ; _×_ )
open import Function                     using () renaming ( Func to _⟶_ )
open import Level                        using ( Level ;  _⊔_ ; Lift )
open import Relation.Binary              using ( IsEquivalence ; Setoid )
open import Relation.Binary.Core         using ()
                                         renaming ( Rel to BinaryRel )
open import Relation.Unary               using ( _∈_; Pred )

-- Imports from agda-algebras -------------------------------------------------------------------

private variable α β ρᵃ ρᵇ ℓ : Level
```
-->

Here is a function that is useful for defining pointwise equality of functions wrt a
given equality.

```agda
open _⟶_ renaming ( to to _⟨$⟩_ )
module _ {𝐴 : Setoid α ρᵃ}{𝐵 : Setoid β ρᵇ} where
  open Setoid 𝐴  using () renaming ( Carrier to A ; _≈_ to _≈₁_ )
  open Setoid 𝐵  using () renaming ( Carrier to B ; _≈_ to _≈₂_ )

  function-equality : BinaryRel (𝐴 ⟶ 𝐵) (α ⊔ ρᵇ)
  function-equality f g = ∀ x → f ⟨$⟩ x ≈₂ g ⟨$⟩ x
```

Here is useful notation for asserting that the image of a function (the first argument)
is contained in a predicate, the second argument (a "subset" of the codomain).

```agda
  Im_⊆_ : (𝐴 ⟶ 𝐵) → Pred B ℓ → Type (α ⊔ ℓ)
  Im f ⊆ S = ∀ x → f ⟨$⟩ x ∈ S
```


#### Kernels on setoids

Given setoids 𝐴 and 𝐵 (with carriers A and B, resp), the *kernel* of a function `f :
𝐴 ⟶ 𝐵` is defined informally by `{(x , y) ∈ A × A : f ⟨$⟩ x ≈₂ f ⟨$⟩ y}`.

```agda
  fker : (𝐴 ⟶ 𝐵) → BinaryRel A ρᵇ
  fker g x y = g ⟨$⟩ x ≈₂ g ⟨$⟩ y

  fkerPred : (𝐴 ⟶ 𝐵) → Pred (A × A) ρᵇ
  fkerPred g (x , y) = g ⟨$⟩ x ≈₂ g ⟨$⟩ y

  open IsEquivalence

  fkerlift : (𝐴 ⟶ 𝐵) → (ℓ : Level) → BinaryRel A (ℓ ⊔ ρᵇ)
  fkerlift g ℓ x y = Lift ℓ (g ⟨$⟩ x ≈₂ g ⟨$⟩ y)

  -- The *identity relation* (equivalently, the kernel of a 1-to-1 function)
  0rel : {ℓ : Level} → BinaryRel A (ρᵃ ⊔ ℓ)
  0rel {ℓ} = λ x y → Lift ℓ (x ≈₁ y)
```
