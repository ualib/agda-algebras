---
layout: default
title : GaloisConnections.Properties module (The Agda Universal Algebra Library)
date : 2021-07-01
author: [the agda-algebras development team][]
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module GaloisConnections.Properties where

open import Agda.Primitive          using    ( _⊔_ ; Level ; lsuc )
                                    renaming ( Set to Type )
open import Data.Product            using    ( _,_ ; _×_ )
                                    renaming ( proj₁ to fst ; proj₂ to snd )
open import Function.Base           using    ( _∘_ ; id )
open import Relation.Binary.Bundles using    ( Poset )
open import Relation.Binary.Core    using    ( REL ; Rel ; _⇒_)
open import Relation.Unary          using    ( _⊆_ ;  _∈_ ; Pred   )
import Relation.Binary.Structures as BS


open import GaloisConnections.Basic using (Galois ; ←→≥id ; →←≥id ; _⃗_ ; _⃖_ )


open Poset


-- Definition of the poset of subsets of a set with the usual set inclusion relation.
-- (I couldn't find this in the standard library, though I suspect it's somewhere.)
module _ {ℓ : Level}{𝒜 : Type ℓ} where

 _≐_ : (P Q : Pred 𝒜 ℓ) → Type ℓ
 P ≐ Q = (P ⊆ Q) × (Q ⊆ P)

 ≐-iseqv : BS.IsEquivalence{a = lsuc ℓ}{ℓ = ℓ}{Pred 𝒜 ℓ} _≐_
 ≐-iseqv = record { refl  = id , id
                  ; sym   = λ x → snd x , fst x
                  ; trans = λ u v → fst v ∘ fst u , snd u ∘ snd v }

 PosetOfSubsets : Poset (lsuc ℓ) ℓ ℓ
 Carrier PosetOfSubsets = Pred 𝒜 ℓ
 _≈_ PosetOfSubsets = _≐_
 _≤_ PosetOfSubsets = _⊆_
 isPartialOrder PosetOfSubsets =
  record { isPreorder = record { isEquivalence = ≐-iseqv
                               ; reflexive = λ P≐Q → fst P≐Q
                               ; trans = λ u v → v ∘ u
                               }
         ; antisym = λ u v → u , v
         }


module _ {ℓ ρ : Level}{𝒜 ℬ : Type ℓ} where

 𝒫𝒜 𝒫ℬ : Poset _ _ _
 𝒫𝒜 = PosetOfSubsets{ℓ}{𝒜}
 𝒫ℬ = PosetOfSubsets{ℓ}{ℬ}


 -- Every binary relation from one poset to another induces a Galois connection.
 Rel→Gal : (R : REL 𝒜 ℬ ℓ) → Galois 𝒫𝒜 𝒫ℬ
 Rel→Gal R = record { F = _⃗ R
                    ; G = R ⃖_
                    ; GF≥id = λ _ → ←→≥id
                    ; FG≥id = λ _ → →←≥id }



\end{code}
