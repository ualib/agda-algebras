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
open import Relation.Unary          using    ( _⊆_ ;  Pred   )

-- Every binary relation induces a Galois connection.


module _ {α β ρ : Level}{𝒜 : Type α}{ℬ : Type β}{R : REL 𝒜 ℬ ρ} where

 -- For A ⊆ 𝒜, define  Inv A = {b : b ∈ ℬ,  ∀ a ∈ A → R a b }
 Inv : (A : Pred 𝒜 (β ⊔ ρ)) → Pred ℬ (α ⊔ ρ)
 Inv A = λ b → ∀ a → R a b

 -- For B ⊆ ℬ, define  Fix B = {a : a ∈ 𝒜,  ∀ b ∈ B → R a b }
 Fix : (B : Pred ℬ (α ⊔ ρ)) → Pred 𝒜 (β ⊔ ρ)
 Fix B = λ a → ∀ b → R a b

 InvFixInv : {A : Pred 𝒜 (β ⊔ ρ)}
  →          Inv (Fix (Inv A)) ⊆ Inv A
 InvFixInv {A = A} {x} p a = p a

 FixInvFix : {B : Pred ℬ (α ⊔ ρ)}
  →          Fix (Inv (Fix B)) ⊆ Fix B
 FixInvFix {B = B} {x} p b = p b

