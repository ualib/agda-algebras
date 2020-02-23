--File: Preliminaries.agda
--Author: William DeMeo and Siva Somayyajula
--Date: 20 Feb 2020 
--Updated: 21 Feb 2020
--Notes: Based on the file `preliminaries.agda` (27 Dec 2019).

{-# OPTIONS --without-K --exact-split #-}

--`without-K` disables Streicher's K axiom; see "Note on axiom K" 
  --            of the ualib documentation (ualib.org).
  --
  --`exact-split` makes Agda to only accept definitions with the
  --              equality sign "=" that behave like so-called
  --              judgmental or definitional equalities.

module Preliminaries where

-- Export common imports
open import Level public renaming (suc to lsuc ; zero to lzero)
open import Data.Empty using (⊥) public
open import Data.Bool using (Bool) public
open import Data.Product using (∃; _,_; _×_) public
  renaming (proj₁ to ∣_∣; proj₂ to ⟦_⟧)
open import Relation.Unary using (Pred; _∈_; _⊆_) public
open import Relation.Binary public
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym) public
open Eq.≡-Reasoning public
open import Function using (_∘_) public
open import Agda.Builtin.Nat public
  renaming ( Nat to ℕ; _-_ to _∸_; zero to nzero; suc to succ )

_∈∈_ : {i j k : Level} {A : Set i} {B : Set j}
  ->   (A -> B)
  ->   Pred B k
      ---------------
  ->   Set (i ⊔ k)
_∈∈_ {A = A} f S = (x : A) -> f x ∈ S

im_⊆_ : {i j k : Level} {A : Set i} {B : Set j}
  ->    (A -> B)
  ->    Pred B k
      -------------------
  ->    Set (i ⊔ k)
im_⊆_ {A = A} f S = (x : A) -> f x ∈ S





  ----------------------------------------------------------------


  ----------------------------
  --EXTENSIONALITY Postulate
  ----------------------------
  --The only way to distinguish functions is by applying them; if two functions
  --applied to the same argument always yield the same result, then they are
  --the same function. It is the converse of cong-app.
  --
  --Agda DOES NOT PRESUME EXTENSIONALITY, but we can POSTULATE that it holds.
  --This postulate is okay since it's CONSISTENT with the theory underlying Agda.

  --------------------------------------
  --Ordinary function extensionality
postulate
  extensionality : ∀ {A B : Set} {f g : A -> B}
    ->             (∀ (x : A) -> f x ≡ g x)
                  --------------------------
    ->             f ≡ g
                   
  --------------------------------------
  --Dependent function extensionality
postulate
  ∀-extensionality :
    ∀ {A : Set} {B : A -> Set} {f g : ∀(x : A) -> B x}
    ->    (∀ (x : A) -> f x ≡ g x)
         -------------------------
    ->    f ≡ g

postulate
  ∀-extensionality-ℓ :
    ∀ {ℓ : Level} {A : Set ℓ} {B : A -> Set ℓ} {f g : ∀(x : A) -> B x}
    ->    (∀ (x : A) -> f x ≡ g x)
         -------------------------
    ->    f ≡ g

postulate
  ∀-extensionality-ℓ₁-ℓ₂ :
    ∀ {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : A -> Set ℓ₂} {f g : ∀(x : A) -> B x}
    ->    (∀ (x : A) -> f x ≡ g x)
         -------------------------
    ->    f ≡ g

postulate
  ∀-extensionality-ℓ₁-ℓ₁⊔ℓ₂ :
    ∀ {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : A -> Set (ℓ₁ ⊔ ℓ₂)} {f g : ∀(x : A) -> B x}
    ->    (∀ (x : A) -> f x ≡ g x)
         -------------------------
    ->    f ≡ g

postulate
  ∀-extensionality-ℓ₁-ℓ₂⊔ℓ₃ :
    ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : A -> Set (ℓ₂ ⊔ ℓ₃)} {f g : ∀(x : A) -> B x}
    ->    (∀ (x : A) -> f x ≡ g x)
         -------------------------
    ->    f ≡ g

postulate
  ∀-extensionality-ℓ₁-ℓ₁⊔ℓ₂⊔ℓ₃ :
    ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : A -> Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)} {f g : ∀(x : A) -> B x}
    ->    (∀ (x : A) -> f x ≡ g x)
         -------------------------
    ->    f ≡ g

  -------------------------------------------------------------
  --Dependent function extensionality (with product codomain)
postulate
  extensionality-dep-× :
    ∀ {A : Set} {B C : A -> Set} {f g : (x : A) -> B x × C x}
      ->   (∀ (x : A) -> ∣ f x ∣ ≡ ∣ g x ∣ -> ⟦ f x ⟧ ≡ ⟦ g x ⟧)
          --------------------------------------------------
      ->   f ≡ g








--=============================================================================
-- MISC NOTES
--============
--
-- When importing `Data.Product` we rename `proj₁` to `∣_∣` and `proj₂` to `⟦_⟧`.
-- If, e.g., `S : Signature i j`, then
--   ∣ S ∣ = the set of operation symbols (which we used to call 𝓕).
--   ⟦ S ⟧ = the arity function (which we used to call ρ).

-------------------------------------------------------------------------------
-- How to write definitions interactively in Agda
-- ----------------------------------------------
--
-- Add a question mark and then type C-c C-l to create a new "hole."
--
-- Type C-c C-f to move into the next unfilled hole.
--
-- Type C-c C-c (from inside the hole) to be prompted for what type should
-- fill the given hole.
--
-- Type m to split on the variable in the hole.
--
-- Type C-c C-f to move into the next hole.
--
-- Type C-c C-, to get the type required in the current hole.
--
-- Enter an appropriate object in the hole; type C-c C-space to remove the hole.
--
-- SUMMARY
--    ? then C-c C-l creates hole
--    C-c C-f moves to next hole
--    C-c C-c prompts for what goes in hole
--    m splits on variable in hole
--    C-c C-, in hole gets type required
--    C-c C-space removes hole
--
------------------------------------
-- Induction
-- ---------
-- For a proof by structural induction over a recursively defined data type,
-- make a hole, enter the hole, type C-c C-c, and when prompted enter the
-- symbol over which you wish to induct.
