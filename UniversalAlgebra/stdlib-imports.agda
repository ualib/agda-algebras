{-
layout: default
title : external-imports module
date : 2021-05-20
author: William DeMeo
-}

-- Imports from the Agda Standard Library
-- ======================================
--
-- This module merely collects all the imports from Agda and the Agda Standard Library
-- that we use throughout the agda-algebras library.

{-# OPTIONS --without-K --exact-split --safe #-}

module stdlib-imports where

open import Agda.Builtin.Bool using (Bool; true; false) public

open import Agda.Primitive using (Level; lsuc; _⊔_)
 renaming ( Set   to  Type                      -- ATTENTION!
          ; Setω  to  Typeω                     -- ATTENTION!
          ; lzero to  ℓ₀                        -- ATTENTION!
          ) public

open import Axiom.Extensionality.Propositional
 renaming (Extensionality to funext             -- ATTENTION!
          ) public

open import Data.Empty public
open import Data.Fin.Base
 renaming (lift to finLift                       -- ATTENTION!
          ) public

open import Data.Nat using (ℕ; zero; suc) public
open import Data.Nat.Properties
 using ( <-irrefl; <-irrelevant; ≤-irrelevant; <⇒≯; <⇒≱; suc-injective
       ; n≤0⇒n≡0; <-transʳ; ≤-reflexive ) public

open import Data.Product using ( _,_ ; Σ ; Σ-syntax ; _×_; ∃; ∃-syntax)
 renaming ( proj₁ to fst                         -- ATTENTION!
          ; proj₂ to snd                         -- ATTENTION!
          ) public

open import Data.Sum.Base using (_⊎_) -- (we might also want [_,_] )
 renaming ( inj₁  to  inl                        -- ATTENTION!
          ; inj₂  to  inr                        -- ATTENTION!
          ) public

open import Data.Unit.Polymorphic.Base public


open import Function.Base using (_∘_; id) public
open import Function.Definitions using (Injective) public
open import Function.Bundles using (_↣_; mk↣) public
open import Function.Construct.Identity using (id-↣) public

open import Level public using ( Lift; lift; lower) public


open import Relation.Binary using (IsEquivalence) public
open import Relation.Binary.Core using (REL; Rel; _⇒_;_=[_]⇒_) public
open import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app; module ≡-Reasoning) public
open ≡-Reasoning public
open import Relation.Nullary using (¬_; Dec; _because_; ofʸ) public
open import Relation.Unary using (∅; Pred; _∪_; _∈_; _⊆_; ｛_｝; ⋂) public

ℓ₁ : Level
ℓ₁ = lsuc ℓ₀
