---
layout: default
title : "Examples.Categories.Functors module (The Agda Universal Algebra Library)"
date : "2021-08-31"
author: "agda-algebras development team"
---

### <a id="functors">Examples of Functors</a>

This is the [Examples.Categories.Functors][] module of the [Agda Universal Algebra Library][].


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Examples.Categories.Functors where

open import Agda.Primitive using ( lsuc ) renaming ( Set to Type ; lzero to ℓ₀ )
open import Data.Nat       using ( ℕ ; zero ; suc ; _>_ )
open import Data.Sum.Base  using ( _⊎_ ) renaming ( inj₁ to inl ;  inj₂ to inr )
open import Data.Product   using ( Σ-syntax ; _,_ ; _×_ )
open import Level
open import Data.Unit      using ( tt ) renaming ( ⊤ to ⊤₀ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; _≢_ )

open import Categories.Functors using ( List ; list ; _⟦_⟧ ; _[_] ; μ_ ; Option )

open μ_
open list

-- Examples
-- 1. Empty list
L₀ : List ℕ
L₀ = inn (inl (Level.lift tt))

l₀ : list ℕ
l₀ = []


-- 2. One-element list, (3)
L₁ : List ℕ
L₁ = inn (inr (3 , L₀))

l₁ : list ℕ
l₁ = 3 ∷ l₀



-- 2. Three-element list, (1, 2, 3)
L₃ : List ℕ
L₃ = inn (inr (1 , (inn (inr (2 , L₀)))))

l₃ : list ℕ
l₃ = 1 ∷ (2 ∷ l₁)

open Option

L₀≡none : ∀ {n} → (L₀ [ n ]) ≡ none
L₀≡none = refl

l₀≡none : ∀ {n} → (l₀ ⟦ n ⟧) ≡ none
l₀≡none = refl


L₁[0]≡some3 : L₁ [ 0 ] ≡ some 3
L₁[0]≡some3 = refl

l₁⟦0⟧≡some3 : l₁ ⟦ 0 ⟧ ≡ some 3
l₁⟦0⟧≡some3 = refl


L₁[n>0]≡none : ∀ n → n > 0 → L₁ [ n ] ≡ none
L₁[n>0]≡none (suc n) _ = refl

l₁⟦n>0⟧≡none : ∀ n → n > 0 → l₁ ⟦ n ⟧ ≡ none
l₁⟦n>0⟧≡none (suc n) _ = refl


L₃[0]≡some1 : L₃ [ 0 ] ≡ some 1
L₃[0]≡some1 = refl

l₃⟦0⟧≡some1 : l₃ ⟦ 0 ⟧ ≡ some 1
l₃⟦0⟧≡some1 = refl


L₃[0]≢some2 : L₃ [ 0 ] ≢ some 2
L₃[0]≢some2 = λ ()

l₃[0]≢some2 : l₃ ⟦ 0 ⟧ ≢ some 2
l₃[0]≢some2 = λ ()

ℓ₁ : Level
ℓ₁ = lsuc ℓ₀

\end{code}
