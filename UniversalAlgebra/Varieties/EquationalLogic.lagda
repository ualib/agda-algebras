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
open import Agda.Builtin.Equality  using    ( _≡_ ;  refl )
open import Agda.Primitive         using    ( _⊔_ ;  lsuc   )
                                   renaming ( Set to Type )
open import Data.Product           using    ( _,_ ; Σ-syntax
                                            ; Σ   ; _×_     )
                                   renaming ( proj₁ to fst
                                            ; proj₂ to snd  )
open import Function.Base          using    ( _∘_ )
open import Relation.Binary.PropositionalEquality
                                   using    ( cong ; cong-app ; module ≡-Reasoning )
open import Relation.Binary        using    ( IsEquivalence    )
                                   renaming (Rel to BinRel)
open import Relation.Binary.PropositionalEquality using  ()
                                   renaming ( sym   to ≡-sym
                                            ; trans to ≡-trans )
open import Relation.Unary         using    ( Pred ; _∈_ ; _⊆_)



-- -- imports from agda-algebras --------------------------------------------------------------
open import Overture.Preliminaries       using ( ∣_∣ ; ∥_∥ ; _⁻¹; _∙_ ; Π ; Π-syntax)
open import Relations.Extensionality     using ( swelldef )
open import Algebras.Products    {𝑆 = 𝑆} using ( ov )
open import Algebras.Congruences {𝑆 = 𝑆} using ( Con ; mkcon)
open import Terms.Basic          {𝑆 = 𝑆} using ( Term ; 𝑻 ; lift-hom )
open import Terms.Operations     {𝑆 = 𝑆} using ( _⟦_⟧ ; subst-lemma ; subst-theorem ; _[_] )
open import Varieties.Basic      {𝑆 = 𝑆} using ( Mod ; Modᵗ ; _⊫_≈_ ; _⊧_≈_)
open Term


module _ {χ : Level}{X : Type χ}{α : Level} where

 -- ℰ ⊢ p ≈ q is valid iff p ≈ q holds in all models that satify all equations in ℰ.
 _⊢_≈_ : Pred(Term X × Term X) (ov α) → Term X → Term X → Type (ov (χ ⊔ α))
 ℰ ⊢ p ≈ q = Mod {α = α} ℰ ⊫ p ≈ q

\end{code}


#### Derivations in a "context" X

This section on derivations was inspired by the types `Sub`, `_[_]`, and `_⊢_▹_≡` Andreas Abel
defined in his Agda formalization of Birkhoff's completeness theorem.
(See: http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf)

\begin{code}

data [_▹_]⊢
 {χ : Level}(X : Type χ)
 {ι : Level}(ℰ : {Y : Type χ} → Pred (Term Y × Term Y) ι) : Pred(Term X × Term X) (ι ⊔ ov χ) where

 base  :  ℰ ⊆ [ X ▹ ℰ ]⊢

 app   :  ∀ op ps qs → (Π[ j ∈ ∥ 𝑆 ∥ op ] ((ps j , qs j) ∈ [ X ▹ ℰ ]⊢))
          → ((node op ps) , (node op qs)) ∈ [ X ▹ ℰ ]⊢

 sub   :  {Y : Type χ}{p q : Term Y}{σ : Y → X} → (p , q) ∈ [ Y ▹ ℰ ]⊢
          →  (p [ σ ] , q [ σ ]) ∈ [ X ▹ ℰ ]⊢

 refl  :  {t : Term X} → (t , t) ∈ [ X ▹ ℰ ]⊢

 sym   :  {p q : Term X} → (p , q) ∈ [ X ▹ ℰ ]⊢  → (q , p) ∈ [ X ▹ ℰ ]⊢

 trans :  {p q r : Term X} → (p , q) ∈ [ X ▹ ℰ ]⊢ → (q , r) ∈ [ X ▹ ℰ ]⊢ → (p , r) ∈ [ X ▹ ℰ ]⊢


\end{code}

#### Soundness of the inference rules

We assume an algebra 𝑨 ∈ Modᵗ ℰ, i.e., an algebra that satisfies all equations in ℰ.

\begin{code}

open ≡-Reasoning
module _ {χ ι : Level}
         {α : Level}(𝑨 : Algebra α 𝑆)
         where

 -- An equality derived from ℰ is an equality in 𝑨 ∈ Modᵗ ℰ.
 sound : swelldef 𝓥 α → {ℰ : {Y : Type χ} → Pred(Term Y × Term Y) (ov α)}
         {X : Type χ}{p q : Term X}
  →      ((Z : Type χ) → 𝑨 ∈ Mod{X = Z} ℰ) → (p , q) ∈ [ X ▹ ℰ ]⊢ → 𝑨 ⊧ p ≈ q

 sound _ {X = X}{p}{q} A⊧ℰ (base x) = A⊧ℰ X p q x
 sound wd A⊧ℰ (app op ps qs x) z = wd (op ̂ 𝑨) (TA ps) (TA qs) λ i → sound wd A⊧ℰ (x i) z
  where
  TA : (ps : ∥ 𝑆 ∥ op → Term _) → ∥ 𝑆 ∥ op → ∣ 𝑨 ∣
  TA ps = λ i → (𝑨 ⟦ ps i ⟧) z

 sound wd A⊧ℰ (sub{Y = Y}{p}{q}{σ} x) a = Goal
  where
  IH : (y : Y → fst 𝑨) → (𝑨 ⟦ p ⟧) y ≡ (𝑨 ⟦ q ⟧) y
  IH y = sound wd {X = Y} A⊧ℰ x y
  Goal : (𝑨 ⟦ p [ σ ] ⟧) a ≡ (𝑨 ⟦ q [ σ ] ⟧) a
  Goal = subst-theorem wd p q σ 𝑨 IH a
 sound _ A⊧ℰ refl = λ z → refl
 sound wd A⊧ℰ (sym x) z = ≡-sym (sound wd A⊧ℰ x z)
 sound wd A⊧ℰ (trans x v) = λ z → ≡-trans (sound wd A⊧ℰ x z) (sound wd A⊧ℰ v z)


\end{code}


The deductive closure of a set ℰ is the set of equations modeled by all models of ℰ; that is, Th Mod ℰ.

The soundness proof above shows ∀ X → ℰ ⊢ X ▹ p ≈ q → (p , q) ∈ Th Mod ℰ.
That is,  ∀ X → ℰ ⊢ X ▹ p ≈ q → Mod ℰ ⊫ p ≈ q.

The converse is Birkhoff's completeness theorem: if Mod ℰ ⊫ p ≈ q, then ℰ ⊢ X ▹ p ≈ q.

(We will prove that result next.)

 -- completeness : ∀ p q → Modᵗ ℰ ⊫ p ≈ q → ℰ ⊢ X ▹ p ≈ q
 -- completeness p q x = Goal
 --  where

 --  Goal : ℰ ⊢ X ▹ p ≈ q
 --  Goal = {!!}



--------------------------------------

[the ualib/agda-algebras development team]: https://github.com/ualib/agda-algebras#the-ualib-agda-algebras-development-team































--  ψ : Pred (∣ 𝑻 X ∣ × ∣ 𝑻 X ∣) (ι ⊔ ov χ)
--  ψ (p , q) = ℰ ⊢ X ▹ p ≈ q

--  ψRel : BinRel ∣ 𝑻 X ∣ (ι ⊔ ov χ)
--  ψRel p q = ψ (p , q)

-- \end{code}

-- To express `ψRel` as a congruence of the term algebra `𝑻 X`, we must prove that

-- 1. `ψRel` is compatible with the operations of `𝑻 X` (which are jsut the terms themselves) and
-- 2. `ψRel` it is an equivalence relation.


--  open ≡-Reasoning

--  ψcompatible : swelldef 𝓥 α → compatible (𝑻 X) ψRel
--  ψcompatible wd 𝑓 {ps} {qs} Ψpq = {!Ψpq!}
--   -- where
--   -- φ : hom (𝑻 X) 𝑨
--   -- φ = lift-hom 𝑨 h

--   -- γ : ∣ φ ∣ ((𝑓 ̂ 𝑻 X) p) ≡ ∣ φ ∣ ((𝑓 ̂ 𝑻 X) q)

--   -- γ = ∣ φ ∣ ((𝑓 ̂ 𝑻 X) p)  ≡⟨ ∥ φ ∥ 𝑓 p ⟩
--   --     (𝑓 ̂ 𝑨) (∣ φ ∣ ∘ p)  ≡⟨ wd (𝑓 ̂ 𝑨)(∣ φ ∣ ∘ p)(∣ φ ∣ ∘ q)(λ x → ψpq x 𝑨 sA h) ⟩
--   --     (𝑓 ̂ 𝑨) (∣ φ ∣ ∘ q)  ≡⟨ (∥ φ ∥ 𝑓 q)⁻¹ ⟩
--   --     ∣ φ ∣ ((𝑓 ̂ 𝑻 X) q)  ∎

--  ψIsEquivalence : IsEquivalence ψRel
--  ψIsEquivalence = record { refl = {!!} -- λ 𝑨 sA h → refl
--                          ; sym = {!!} -- λ x 𝑨 sA h → (x 𝑨 sA h)⁻¹
--                          ; trans = {!!} -- λ pψq qψr 𝑨 sA h → (pψq 𝑨 sA h) ∙ (qψr 𝑨 sA h) }
--                          }
-- \end{code}

-- We have collected all the pieces necessary to express the collection of identities satisfied by all subalgebras of algebras in the class as a congruence relation of the term algebra. We call this congruence `ψCon` and define it using the Congruence constructor `mkcon`.


--  ψCon : swelldef 𝓥 α → Con (𝑻 X)
--  ψCon wd = ψRel , mkcon ψIsEquivalence (ψcompatible wd)

-- \end{code}


