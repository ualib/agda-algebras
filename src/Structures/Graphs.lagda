---
layout: default
title : Structures.Graphs module
date : 2021-06-22
author: [agda-algebras development team][]
---

N.B. This module differs from 0Graphs.lagda in that this module is universe polymorphic; i.e., we do not restrict universe levels (to, e.g., ℓ₀). This complicates some things; e.g., we must use lift and lower in some places (cf. 0Graphs.lagda).

Definition [Graph of a structure]. Let 𝑨 be an (𝑅,𝐹)-structure (relations from 𝑅 and operations from 𝐹).
The *graph* of 𝑨 is the structure Gr 𝑨 with the same domain as 𝑨 with relations from 𝑅 and together with a (k+1)-ary relation symbol G 𝑓 for each 𝑓 ∈ 𝐹 of arity k, which is interpreted in Gr 𝑨 as all tuples (t , y) ∈ Aᵏ⁺¹ such that 𝑓 t ≡ y. (See also Definition 2 of https://arxiv.org/pdf/2010.04958v2.pdf)


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Structures.Graphs where

open import Agda.Primitive         using    ( _⊔_ ; lsuc ; Level )
                                   renaming ( Set to Type ; lzero  to ℓ₀ )
open import Agda.Builtin.Equality  using    ( _≡_ ; refl )
open import Data.Product           using    ( _,_ ; Σ-syntax ; _×_ )
open import Data.Sum.Base          using    ( _⊎_ )
                                   renaming ( inj₁ to inl ; inj₂ to inr )
open import Level                  using    ( Lift ; lift ; lower )
open import Function.Base          using    ( _∘_  )
import Relation.Binary.PropositionalEquality as PE


-- Imports from agda-algebras --------------------------------------------------------------
open import Overture.Preliminaries   using ( ∣_∣ ; _≈_ ; ∥_∥ ; _∙_ ; lower∼lift ; lift∼lower ; 𝟙)
open import Relations.Continuous     using ( Rel )
open import Structures.Basic         using ( signature ; structure )
open import Examples.Structures.Signatures
                                     using ( S∅ )
open import Structures.Homs          using ( hom ; 𝒾𝒹 ; ∘-hom ; 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇 ; is-hom-rel; is-hom-op)

open signature
open structure
open _⊎_


Gr-sig : signature ℓ₀ ℓ₀ → signature ℓ₀ ℓ₀ → signature ℓ₀ ℓ₀

Gr-sig 𝐹 𝑅 = record { symbol = symbol 𝑅 ⊎ symbol 𝐹
                    ; arity  = ar }
 where
 ar : symbol 𝑅 ⊎ symbol 𝐹 → Type _
 ar (inl 𝑟) = (arity 𝑅) 𝑟
 ar (inr 𝑓) = (arity 𝐹) 𝑓 ⊎ 𝟙

private variable
 𝐹 𝑅 : signature ℓ₀ ℓ₀
 α ρ : Level

Gr : ∀{α ρ} → structure 𝐹 𝑅 {α} {ρ} → structure S∅ (Gr-sig 𝐹 𝑅) {α} {α ⊔ ρ}
Gr {𝐹}{𝑅}{α}{ρ} 𝑨 = record { carrier = carrier 𝑨 ; op = λ () ; rel = split }
  where
  split : (s : symbol 𝑅 ⊎ symbol 𝐹) → Rel (carrier 𝑨) (arity (Gr-sig 𝐹 𝑅) s) {α ⊔ ρ}
  split (inl 𝑟) arg = Lift α (rel 𝑨 𝑟 arg)
  split (inr 𝑓) args = Lift ρ (op 𝑨 𝑓 (args ∘ inl) ≡ args (inr 𝟙.𝟎))


open PE.≡-Reasoning

private variable
 ρᵃ β ρᵇ : Level

module _ {𝑨 : structure 𝐹 𝑅 {α} {ρᵃ}}
         {𝑩 : structure 𝐹 𝑅 {β} {ρᵇ}} where

 hom→Grhom : hom 𝑨 𝑩 → hom (Gr 𝑨) (Gr 𝑩)
 hom→Grhom (h , hhom) = h , (i , ii)
  where
  i : is-hom-rel (Gr 𝑨) (Gr 𝑩) h
  i (inl 𝑟) a x = lift (∣ hhom ∣ 𝑟 a (lower x))
  i (inr 𝑓) a x = lift goal
   where
   homop : h (op 𝑨 𝑓 (a ∘ inl)) ≡ op 𝑩 𝑓 (h ∘ (a ∘ inl))
   homop = ∥ hhom ∥ 𝑓 (a ∘ inl)

   goal : op 𝑩 𝑓 (h ∘ (a ∘ inl)) ≡ h (a (inr 𝟙.𝟎))
   goal = op 𝑩 𝑓 (h ∘ (a ∘ inl)) ≡⟨ PE.sym homop ⟩
          h (op 𝑨 𝑓 (a ∘ inl))   ≡⟨ PE.cong h (lower x) ⟩
          h (a (inr 𝟙.𝟎))         ∎

  ii : is-hom-op (Gr 𝑨) (Gr 𝑩) h
  ii = λ ()


 Grhom→hom : hom (Gr 𝑨) (Gr 𝑩) → hom 𝑨 𝑩
 Grhom→hom (h , hhom) = h , (i , ii)
  where
  i : is-hom-rel 𝑨 𝑩 h
  i R a x = lower (∣ hhom ∣ (inl R) a (lift x))
  ii : is-hom-op 𝑨 𝑩 h
  ii f a = goal -- goal
   where
   split : arity 𝐹 f ⊎ 𝟙 → carrier 𝑨
   split (inl x) = a x
   split (inr y) = op 𝑨 f a
   goal : h (op 𝑨 f a) ≡ op 𝑩 f (λ x → h (a x))
   goal = PE.sym (lower (∣ hhom ∣ (inr f) split (lift refl)))


\end{code}

------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

