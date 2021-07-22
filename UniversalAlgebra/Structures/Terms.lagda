---
layout: default
title : Structures.Terms
date : 2021-07-02
author: [agda-algebras development team][]
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Structures.Terms where

open import Agda.Primitive using    ( lsuc ; Level ; _⊔_ )
                           renaming ( Set to Type ; lzero to ℓ₀ )
open import Data.Fin.Base  using    ( Fin )
open import Data.Nat       using    ( ℕ )
open import Data.Product   using    ( _,_ ;  _×_ )
                           renaming ( proj₁ to fst ; proj₂ to snd )
open import Relation.Unary using    ( Pred ; _∈_ )


-- Imports from agda-algebras --------------------------------------
open import Overture.Preliminaries  using ( _≈_ )
open import Structures.Basic        using ( signature ; structure )

private variable
 𝓞 𝓥 : Level

module _ {𝐹 : signature 𝓞 𝓥} {χ : Level} where

 open signature

 data Term (X : Type χ ) : Type (𝓞 ⊔ 𝓥 ⊔ (lsuc χ))  where
  ℊ : X → Term X    -- (ℊ for "generator")
  node : (f : symbol 𝐹)(𝑡 : (arity 𝐹) f → Term X) → Term X

\end{code}

When we interpret a term in a structure we call the resulting
function a *term operation*. Given a term `p` and a structure `𝑨`,
we denote by `𝑨 ⟦ p ⟧` the *interpretation* of `p` in `𝑨`.
This is defined inductively as follows.

1. If `p` is a variable symbol `x : X` and if `a : X → ∣ 𝑨 ∣`
   is a tuple of elements of `∣ 𝑨 ∣`, then `𝑨 ⟦ p ⟧ a := a x`.

2. If `p = 𝑓 𝑡`, where `𝑓 : ∣ 𝑆 ∣` is an operation symbol,
   if `𝑡 : ∥ 𝑆 ∥ 𝑓 → 𝑻 X` is a tuple of terms, and if
   `a : X → ∣ 𝑨 ∣` is a tuple from `𝑨`, then we define
   `𝑨 ⟦ p ⟧ a = 𝑨 ⟦ 𝑓 𝑡 ⟧ a := (𝑓 ̂ 𝑨) (λ i → 𝑨 ⟦ 𝑡 i ⟧ a)`.

Thus interpretation of a term is defined by structural induction.

\begin{code}

private variable
 𝓞₀ 𝓥₀ 𝓞₁ 𝓥₁ : Level
 𝐹 : signature 𝓞₀ 𝓥₀
 𝑅 : signature 𝓞₁ 𝓥₁
 χ : Level
 X : Type χ
 α ρ ℓ : Level

open structure

_⟦_⟧ : (𝑨 : structure 𝐹 𝑅 {α} {ρ}) → Term X → (X → carrier 𝑨) → carrier 𝑨
𝑨 ⟦ ℊ x ⟧ = λ η → η x
𝑨 ⟦ node 𝑓 𝑡 ⟧ = λ η → ((op 𝑨) 𝑓) (λ i → (𝑨 ⟦ 𝑡 i ⟧) η)

\end{code}


#### Entailment, equational theories, and models


\begin{code}

_⊧_≈_ : structure 𝐹 𝑅 {α}{ρ} → Term X → Term X → Type _
𝑨 ⊧ p ≈ q = 𝑨 ⟦ p ⟧ ≈ 𝑨 ⟦ q ⟧

_⊧_≋_ : Pred(structure 𝐹 𝑅 {α}{ρ}) ℓ → Term X → Term X → Type _
𝒦 ⊧ p ≋ q = ∀{𝑨 : structure _ _} → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q

-- Theories
Th : Pred (structure 𝐹 𝑅{α}{ρ}) ℓ → Pred(Term X × Term X) _ -- (ℓ₁ ⊔ χ)
Th 𝒦 = λ (p , q) → 𝒦 ⊧ p ≋ q

-- Models
Mod : Pred(Term X × Term X) ℓ  → Pred(structure 𝐹 𝑅 {α} {ρ}) _  -- (χ ⊔ ℓ₀)
Mod ℰ = λ 𝑨 → ∀ p q → (p , q) ∈ ℰ → 𝑨 ⊧ p ≈ q

fMod : {n : ℕ} → (Fin n → (Term X × Term X)) → Pred(structure 𝐹 𝑅 {α} {ρ}) _
fMod ℰ = λ 𝑨 → ∀ i → 𝑨 ⊧ fst (ℰ i) ≈ snd (ℰ i)

\end{code}


------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team


\end{code}

------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
