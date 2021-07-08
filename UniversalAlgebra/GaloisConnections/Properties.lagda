---
layout: default
title : GaloisConnections.Properties module (The Agda Universal Algebra Library)
date : 2021-07-01
author: [the agda-algebras development team][]
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module GaloisConnections.Properties where

open import Agda.Primitive          using    ( _⊔_ ;  Level  )
                                    renaming ( Set to Type   )
open import Relation.Binary.Core    using    ( REL )
open import Relation.Unary          using    ( _⊆_ ;  _∈_ ; Pred   )

-- Every binary relation induces a Galois connection.

module _ {α β ρ : Level}{𝒜 : Type α}{ℬ : Type β}{R : REL 𝒜 ℬ ρ} where


 -- For A ⊆ 𝒜, define  Inv A = {b : b ∈ ℬ,  ∀ a ∈ A → R a b }
 Inv : (A : Pred 𝒜 (α ⊔ β ⊔ ρ)) → Pred ℬ (α ⊔ β ⊔ ρ)
 Inv A = λ b → (a : 𝒜) → a ∈ A → R a b

 -- For B ⊆ ℬ, define  Fix B = {a : a ∈ 𝒜,  ∀ b ∈ B → R a b }
 Fix : (B : Pred ℬ (α ⊔ β ⊔ ρ)) → Pred 𝒜 (α ⊔ β ⊔ ρ)
 Fix B = λ a → (b : ℬ) → b ∈ B → R a b

 FixInv : {A : Pred 𝒜 (α ⊔ β ⊔ ρ)} → A ⊆ Fix (Inv A)
 FixInv p b InvAb = InvAb _ p

 InvFix : {B : Pred ℬ (α ⊔ β ⊔ ρ)} → B ⊆ Inv (Fix B)
 InvFix p a FixBa = FixBa _ p

 InvFixInv : {A : Pred 𝒜 (α ⊔ β ⊔ ρ)} → Inv (Fix (Inv A)) ⊆ Inv A
 InvFixInv p a Aa = p a (λ b z → z a Aa)

 FixInvFix : {B : Pred ℬ (α ⊔ β ⊔ ρ)} → Fix (Inv (Fix B)) ⊆ Fix B
 FixInvFix p b Bb = p b (λ a z → z b Bb)

\end{code}
