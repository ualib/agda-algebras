---
layout: default
title : Varieties.EquationalLogic module (The Agda Universal Algebra Library)
date : 2021-01-14
author: [the ualib/agda-algebras development team][]
---

This is the [Varieties.EquationalLogic][] module of the [Agda Universal Algebra Library][].

### Entailment, derivation rules, soundness and completeness

For a tuple or set ℰ of term equations (pairs of terms) we say ℰ *entails* p ≈ q and we write ℰ ⊢ p ≈ q just in case p ≈ q holds in all models of ℰ.

**Unicode Hints**. In [agda2-mode][], type `\entails`, and `\~~` to get ⊢ and ≈, respectively.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


open import Level using ( Level )
open import Algebras.Basic

module Varieties.EquationalLogic {𝑆 : Signature 𝓞 𝓥} where


-- imports from Agda and the Agda Standard Library -------------------------------------------
open import Agda.Primitive         using    ( _⊔_ ;  lsuc   )
                                   renaming ( Set to Type
                                            ; lzero to  ℓ₀  )
open import Data.Product           using    ( _,_ ; Σ-syntax
                                            ; Σ   ; _×_     )
                                   renaming ( proj₁ to fst
                                            ; proj₂ to snd  )
open import Relation.Unary         using    ( Pred )



-- -- imports from agda-algebras --------------------------------------------------------------
open import Overture.Preliminaries       using ( ∣_∣ ; ∥_∥ )
open import Algebras.Products    {𝑆 = 𝑆} using ( ov )
open import Terms.Basic          {𝑆 = 𝑆} using ( Term ; 𝑻 ; lift-hom )
open import Varieties.Basic      {𝑆 = 𝑆} using ( Mod ; Modᵗ ; _⊫_≈_ )
open Term


module _ {χ : Level}{X : Type χ}{α : Level} where

 -- ℰ ⊢ p ≈ q is valid iff p ≈ q holds in all models that satify all equations in ℰ.
 _⊢_≈_ : Pred(Term X × Term X) (ov α) → Term X → Term X → Type (ov (χ ⊔ α))
 ℰ ⊢ p ≈ q = Mod {α = α} ℰ ⊫ p ≈ q

\end{code}


#### Derivations in a "context" X

This section on derivations is an adaptation of Andreas Abel's `Sub`, `_[_]`, and `_⊢_▹_≡` types.

Quoting Abel, "Equalitional logic allows us to prove entailments via the inference rules for the judgment E ⊢ Γ ▹ p ≡ q. This could be coined as equational theory over a given set of equations $E$. Relation E ⊢ Γ ▹ _≡_ is the least congruence over the equations E."

\begin{code}

-- Substitutions. A substitution from Y to X holds a term in X for each variable in Y.
Subst : {χ : Level}(Y X : Type χ) → Type _
Subst Y X = (x : X) → Term Y

-- Application of a substitution.
_[_] : {χ : Level}{Y X : Type χ}(t : Term Y) (σ : Subst X Y) → Term X
(ℊ x) [ σ ] = σ x
(node 𝑓 t)  [ σ ] = node 𝑓 λ i → t i [ σ ]

module _ {γ ι : Level}{I : Type ι} where

 private variable
  Γ Δ : Type γ
  p q r :  Term Γ
  op : ∣ 𝑆 ∣
  ts ts' : {Γ : Type γ}(i : ∥ 𝑆 ∥ op) → Term Γ

 data _⊢_▹_≈_
  (ℰ : {X : Type γ} → I → Term X × Term X) : (Γ : Type γ)(p q : Term Γ) → Type (ι ⊔ ov γ) where
  hyp   :  ∀ i                               → ℰ ⊢ Γ ▹ (fst (ℰ i)) ≈ (snd (ℰ i))
  base  :  ∀ (x : Γ)                         → ℰ ⊢ Γ ▹ ℊ x ≈ ℊ x
  app   :  (∀ i → ℰ ⊢ Γ ▹ ts i ≈ ts' i)      → ℰ ⊢ Γ ▹ (node op ts) ≈ (node op ts')
  sub   :  ℰ ⊢ Γ ▹ p ≈ q → ∀ (σ : Subst Δ Γ) → ℰ ⊢ Δ ▹ (p [ σ ]) ≈ (q [ σ ])
  refl  :  ∀ (t : Term Γ)                    → ℰ ⊢ Γ ▹ t ≈ t
  sym   :  ℰ ⊢ Γ ▹ p ≈ q                     → ℰ ⊢ Γ ▹ q ≈ p
  trans :  ℰ ⊢ Γ ▹ p ≈ q → ℰ ⊢ Γ ▹ q ≈ r     → ℰ ⊢ Γ ▹ p ≈ r


-- Soundness of the inference rules
-- We assume an algebra 𝑨 ∈ Modᵗ ℰ, i.e., an algebra that satisfies all equations in ℰ.
-- module _ {χ : Level}{X Y : Type χ}
--          {ι : Level}{I : Type ι}
--          (ℰ : {Y : Type χ} → I → Term Y × Term Y)
--          {α : Level}(𝑨 : Algebra α 𝑆)
--          (A⊧ℰ : 𝑨 ∈ Modᵗ{χ}{X} ℰ) where

--  private variable p q r : Term X

--  -- If 𝑨 ∈ Modᵗ ℰ, then derived equality is actual equality.
--  -- (we'll prove this next (24 June))
--  sound : swelldef 𝓥 α → ℰ ⊢ X ▹ p ≈ q → 𝑨 ⊧ p ≈ q

--  sound _ (hyp i) = A⊧ℰ i
--  sound _ (base x) = λ _ → refl
--  sound wd (app {op = op}{ts}{ts'} x) =
--   λ a → wd (op ̂ 𝑨) (λ i → (𝑨 ⟦ ts i ⟧) a) (λ i → (𝑨 ⟦ ts' i ⟧) a) λ i → sound wd (x i) a
--  sound - (sub{X}{p}{q} x σ) a = Goal
--   where
--   -- ξ : (𝑨 ⟦ p ⟧) a ≡ (𝑨 ⟦ q ⟧) a
--   -- ξ = ?
--   Goal : (𝑨 ⟦ p [ σ ] ⟧) a ≡ (𝑨 ⟦ q [ σ ] ⟧) a
--   Goal = {!!}
-- -- _⟦_⟧ : (𝑨 : Algebra α 𝑆){X : Type 𝓧 } → Term X → (X → ∣ 𝑨 ∣) → ∣ 𝑨 ∣
-- -- 𝑨 ⟦ ℊ x ⟧ = λ η → η x
-- -- 𝑨 ⟦ node 𝑓 𝑡 ⟧ = λ η → (𝑓 ̂ 𝑨) (λ i → (𝑨 ⟦ 𝑡 i ⟧) η)
--  sound - (refl _) = λ _ → refl
--  sound - (sym x) = {!!}
--  sound - (trans x x₁) = {!!}
 
\end{code}



--------------------------------------

[the ualib/agda-algebras development team]: https://github.com/ualib/agda-algebras#the-ualib-agda-algebras-development-team
