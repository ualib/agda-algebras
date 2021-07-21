---
layout: default
title : Structures.Terms.Basic
date : 2021-07-02
author: [agda-algebras development team][]
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Structures.Terms.Basic where

open import Agda.Primitive      using ( lsuc ; Level ; _⊔_ ) renaming ( Set to Type ; lzero to ℓ₀ )

open import Structures.Records  using ( signature ; structure )

open signature
open structure


module _ {𝓞 𝓥 : Level}
         {𝐹 : signature 𝓞 𝓥}
         {χ : Level} where

 data Term (X : Type χ ) : Type (𝓞 ⊔ 𝓥 ⊔ (lsuc χ))  where
  ℊ : X → Term X    -- (ℊ for "generator")
  node : (f : symbol 𝐹)(𝑡 : (arity 𝐹) f → Term X) → Term X

 open Term public

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
 α ρ : Level


_⟦_⟧ : (𝑨 : structure 𝐹 𝑅 {α} {ρ}) → Term X → (X → carrier 𝑨) → carrier 𝑨
𝑨 ⟦ ℊ x ⟧ = λ η → η x
𝑨 ⟦ node 𝑓 𝑡 ⟧ = λ η → ((op 𝑨) 𝑓) (λ i → (𝑨 ⟦ 𝑡 i ⟧) η)


\end{code}

------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
