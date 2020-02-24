--File: basic.agda
--Author: William DeMeo
--Date: 24 Dec 2019
--Updated: 10 Jan 2020
--Note: This was used for the first part of my talk at JMM Special Session.

{-# OPTIONS --without-K --exact-split #-}

--without-K disables Streicher's K axiom (see "NOTES on Axiom K" below).

--exact-split makes Agda to only accept definitions with the equality sign "=" that
--behave like so-called judgmental or definitional equalities.

module basic where

open import Level
open import preliminaries using (Bool)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function using (_∘_)
open import Data.Product using (∃; Σ; _,_)

-----------------------------
--A data type for OPERATIONS
-- Prefer this to operation b/c
-- no superfluous constructors
-----------------------------
module _ {i j} where
  Op : Set i → Set j → Set (i ⊔ j)
  Op I A = (I → A) → A

  π : {I : Set i} {A : Set j} -> I -> Op I A
  π i x = x i

--------------------------------
-- A data type for SIGNATURES
--------------------------------

record Signature (i j : Level) : Set (suc (i ⊔ j)) where
  constructor sig
  field
    F : Set i       -- Operation symbols
    ρ : F → Set j   -- Each operation symbol has an arity

data Void {i} : Set i where

data monoid-op : Set where
  e : monoid-op
  · : monoid-op

monoid-sig : Signature zero zero
monoid-sig = sig monoid-op λ
  { e → Void;
    · → Bool }

-----------------------------
--A data type for ALGEBRAS
-----------------------------

variable i j : Level

record Algebra (k : Level) (S : Signature i j) : Set (i ⊔ j ⊔ suc k) where
-- an algebra is just (alg carrier interp)
  constructor alg
  open Signature S
  infixl 20 _⟦_⟧
  field
    ∣_∣₀ : Set k
    _⟦_⟧ : (o : F) → Op (ρ o) ∣_∣₀

----------------------------------
--A data type for HOMOMORPHISMS
----------------------------------

record Hom {i j k} {S : Signature i j} (A B : Algebra k S) : Set {!!} where
  constructor hom
  open Algebra
  open Signature S
  field
    ∣_∣₁ : ∣ A ∣₀ → ∣ B ∣₀

    -- The property the map must have to be a hom
    -- i.e. the map factors through interpretation
    is-hom : ∀ {o : F} (x : ρ o → ∣ A ∣₀) →
      ∣_∣₁ ((A ⟦ o ⟧) x) ≡ (B ⟦ o ⟧) (∣_∣₁ ∘ x)

