---
layout: default
title : Structures.Graphs
date : 2021-06-22
author: William DeMeo
---

N.B. This module differs from AsRecordsGraphs.lagda in that we assume some universes are lzero (i.e., ℓ₀).

This module implements the graph of a structure.  (See Definition 2 of https://arxiv.org/pdf/2010.04958v2.pdf )

Definition [Graph of a structure]. Let 𝑨 be an (𝑅,𝐹)-structure (relations from 𝑅 and operations from 𝐹).
The *graph* of 𝑨 is the structure Gr 𝑨 with the same domain as 𝑨 with relations from 𝑅 and together with a (k+1)-ary relation symbol G 𝑓 for each 𝑓 ∈ 𝐹 of arity k, which is interpreted in Gr 𝑨 as all tuples (t , y) ∈ Aᵏ⁺¹ such that 𝑓 t ≡ y.



\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Structures.Graphs where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Agda.Primitive                        using    ( _⊔_    ;   lsuc     )
                                                  renaming ( Set    to  Type
                                                           ; lzero  to ℓ₀        )
open import Agda.Builtin.Equality                 using    ( _≡_    ;   refl     )
open import Data.Sum.Base                         using    ( _⊎_                 )
                                                  renaming ( inj₁   to inl
                                                           ; inj₂   to inr       )
open import Data.Product                          using    ( _,_    ;   Σ-syntax
                                                           ;  Σ     ;   _×_      )
                                                  renaming ( proj₁  to  fst
                                                           ; proj₂  to  snd      )
open import Level                                 using    ( Level  ;  Lift
                                                           ; lift   ;  lower     )
open import Function.Base                         using    ( _∘_                 )
open import Relation.Binary.PropositionalEquality using    ( cong   ; sym
                                                           ; module ≡-Reasoning  )
open import Relation.Unary                        using    ( Pred   ; _∈_        )


-- Imports from agda-algebras --------------------------------------------------------------
open import Overture.Preliminaries     using ( ∣_∣ ; _≈_ ; ∥_∥ ; _∙_ ; lower∼lift ; lift∼lower ; 𝟙)
open import Structures.AsRecordsBasic  using ( signature ; structure ; Sig∅) -- ; Lift-Struc )
open import Structures.AsRecordsHoms   using ( hom ; 𝒾𝒹 ; ∘-hom ; 𝓁𝒾𝒻𝓉 ; 𝓁ℴ𝓌ℯ𝓇 ; is-hom-rel; is-hom-op)
open import Relations.Continuous       using ( Rel )
open import Relations.Extensionality   using ( _≐_ )

open signature
open structure
open _⊎_

ℓ₁ : Level
ℓ₁ = lsuc ℓ₀

Gr-sig : signature → signature → signature
Gr-sig 𝐹 𝑅 = record { symbol = symbol 𝑅 ⊎ symbol 𝐹 ; arity = arty }
 where
 arty : symbol 𝑅 ⊎ symbol 𝐹 → Type ℓ₀
 arty (inl 𝑟) = (arity 𝑅) 𝑟
 arty (inr 𝑓) = (arity 𝐹) 𝑓 ⊎ 𝟙


module _ {𝐹 𝑅 : signature} where

 Gr : structure 𝐹 {ℓ₀} 𝑅 {ℓ₀} → structure Sig∅ {ℓ₀} (Gr-sig 𝐹 𝑅) {ℓ₀}
 Gr 𝑨 = record { carrier = carrier 𝑨 ; op = λ () ; rel = split }
  where
  split : (s : symbol 𝑅 ⊎ symbol 𝐹) → Rel (carrier 𝑨) (arity (Gr-sig 𝐹 𝑅) s) {ℓ₀}
  split (inl 𝑟) arg = rel 𝑨 𝑟 arg
  split (inr 𝑓) args = op 𝑨 𝑓 (args ∘ inl) ≡ args (inr 𝟙.𝟎)


open ≡-Reasoning

module _ {𝐹 𝑅 : signature}
         {𝑨 𝑩 : structure 𝐹 {ℓ₀} 𝑅 {ℓ₀}} where

 hom→Grhom : hom 𝑨 𝑩 → hom (Gr 𝑨) (Gr 𝑩)
 hom→Grhom (h , hhom) = h , (i , ii)
  where
  i : is-hom-rel (Gr 𝑨) (Gr 𝑩) h
  i (inl 𝑟) a x = ∣ hhom ∣ 𝑟 a x
  i (inr 𝑓) a x = goal
   where
   homop : h (op 𝑨 𝑓 (a ∘ inl)) ≡ op 𝑩 𝑓 (h ∘ (a ∘ inl))
   homop = (snd hhom) 𝑓 (a ∘ inl)

   goal : op 𝑩 𝑓 (h ∘ (a ∘ inl)) ≡ h (a (inr 𝟙.𝟎))
   goal = op 𝑩 𝑓 (h ∘ (a ∘ inl)) ≡⟨ sym homop ⟩
          h (op 𝑨 𝑓 (a ∘ inl))   ≡⟨ cong h x ⟩
          h (a (inr 𝟙.𝟎))         ∎

  ii : is-hom-op (Gr 𝑨) (Gr 𝑩) h
  ii = λ ()


 Grhom→hom : hom (Gr 𝑨) (Gr 𝑩) → hom 𝑨 𝑩
 Grhom→hom (h , hhom) = h , (i , ii)
  where
  i : is-hom-rel 𝑨 𝑩 h
  i R a x = fst hhom (inl R) a x
  ii : is-hom-op 𝑨 𝑩 h
  ii f a = goal
   where
   split : arity 𝐹 f ⊎ 𝟙 → carrier 𝑨
   split (inl x) = a x
   split (inr y) = op 𝑨 f a
   goal : h (op 𝑨 f a) ≡ op 𝑩 f (λ x → h (a x))
   goal = sym (fst hhom (inr f) split refl)



{- Lemma III.1. Let S be a signature and A be an S-structure.
Let Σ be a finite set of identities such that A ⊧ Σ. For every
instance X of CSP(A), one can compute in polynomial time an
instance Y of CSP(A) such that Y ⊧ Σ and | Hom(X , A)| = |Hom(Y , A)|. -}


module _ {𝐹 : signature}{χ : Level} where

 data Term (X : Type χ ) : Type χ  where
  ℊ : X → Term X    -- (ℊ for "generator")
  node : (f : symbol 𝐹)(𝑡 : (arity 𝐹) f → Term X) → Term X

 open Term public

\end{code}

When we interpret a term in a structure we call the resulting function a *term operation*.  Given a term `p` and a structure `𝑨`, we denote by `𝑨 ⟦ p ⟧` the *interpretation* of `p` in `𝑨`.  This is defined inductively as follows.

1. If `p` is a variable symbol `x : X` and if `a : X → ∣ 𝑨 ∣` is a tuple of elements of `∣ 𝑨 ∣`, then `𝑨 ⟦ p ⟧ a := a x`.

2. If `p = 𝑓 𝑡`, where `𝑓 : ∣ 𝑆 ∣` is an operation symbol, if `𝑡 : ∥ 𝑆 ∥ 𝑓 → 𝑻 X` is a tuple of terms, and if `a : X → ∣ 𝑨 ∣` is a tuple from `𝑨`, then we define `𝑨 ⟦ p ⟧ a = 𝑨 ⟦ 𝑓 𝑡 ⟧ a := (𝑓 ̂ 𝑨) (λ i → 𝑨 ⟦ 𝑡 i ⟧ a)`.

Thus the interpretation of a term is defined by induction on the structure of the term, and the definition is formally implemented as follows.

\begin{code}

module _ {𝐹 𝑅 : signature}{χ : Level}{X : Type χ} where

 _⟦_⟧ : (𝑨 : structure 𝐹 {ℓ₀} 𝑅 {ℓ₀}) → Term X → (X → carrier 𝑨) → carrier 𝑨
 𝑨 ⟦ ℊ x ⟧ = λ η → η x
 𝑨 ⟦ node 𝑓 𝑡 ⟧ = λ η → ((op 𝑨) 𝑓) (λ i → (𝑨 ⟦ 𝑡 i ⟧) η)

 _⊧_≈_ : structure 𝐹 𝑅 → Term X → Term X → Type _
 𝑨 ⊧ p ≈ q = 𝑨 ⟦ p ⟧ ≈ 𝑨 ⟦ q ⟧

 _⊧_≋_ : Pred(structure 𝐹 𝑅) ℓ₀ → Term X → Term X → Type _
 𝒦 ⊧ p ≋ q = {𝑨 : structure 𝐹 𝑅} → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q


 Th : Pred (structure 𝐹 𝑅) ℓ₀ → Pred(Term X × Term X) (ℓ₁ ⊔ χ)
 Th 𝒦 = λ (p , q) → 𝒦 ⊧ p ≋ q

 Mod : Pred(Term X × Term X) (χ ⊔ ℓ₀) → Pred(structure 𝐹 {ℓ₀} 𝑅 {ℓ₀}) χ
 Mod ℰ = λ 𝑨 → ∀ p q → (p , q) ∈ ℰ → 𝑨 ⊧ p ≈ q

 fMod : {n : ℕ} → (Fin n → (Term X × Term X)) → Pred(structure 𝐹 {ℓ₀} 𝑅 {ℓ₀}) χ
 fMod ℰ = λ 𝑨 → ∀ i → 𝑨 ⊧ fst (ℰ i) ≈ snd (ℰ i)

\end{code}

The entailment ℰ ⊢ p ≈ q is valid iff p ≈ q holds in all models that satify all equations in ℰ.

\begin{code}

module _ {𝐹 𝑅 : signature} where

 record _⇛_⇚_ (𝑩 𝑨 𝑪 : structure 𝐹 𝑅) : Type ℓ₀ where
  field
   to   : hom 𝑩 𝑨 → hom 𝑪 𝑨
   from : hom 𝑪 𝑨 → hom 𝑩 𝑨
   to∼from : ∀ h → (to ∘ from) h ≡ h
   from∼to : ∀ h → (from ∘ to) h ≡ h



module _ {𝐹 𝑅 : signature}{χ : Level}{X : Type χ}
         {𝑨 : structure 𝐹 {ℓ₀} 𝑅 {ℓ₀}} where


 -- LEMMAIII1 : (ℰ : Pred (Term X × Term X) (ℓ₀ ⊔ χ))
 --  →          (𝑨 ∈ Mod ℰ)
 --  →          ∀(𝑩 : structure 𝐹 𝑅)
 --  →          Σ[ 𝑪 ∈ structure 𝐹 𝑅 ] (𝑪 ∈ Mod ℰ × (𝑩 ⇛ 𝑨 ⇚ 𝑪))
 -- LEMMAIII1 ℰ 𝑨⊧ℰ 𝑩 = {!!} , {!!}

 -- LEMMAIII1 : {n : ℕ}(ℰ : Fin n → (Term X × Term X))
 --  →          (𝑨 ∈ fMod ℰ)
 --  →          ∀(𝑩 : structure 𝐹 𝑅)
 --  →          Σ[ 𝑪 ∈ structure 𝐹 𝑅 ] (𝑪 ∈ fMod ℰ × (𝑩 ⇛ 𝑨 ⇚ 𝑪))
 -- LEMMAIII1 ℰ 𝑨⊧ℰ 𝑩 = {!!} , {!!}

\end{code}


