---
layout: default
title : Varieties.Setoid.EquationalLogic module (The Agda Universal Algebra Library)
date : 2021-01-14
author: [agda-algebras development team][]
---

This is the [Varieties.EquationalLogic][] module of the [Agda Universal Algebra Library][].

### Entailment, derivation rules, soundness and completeness

This module is based on Andreas Abel's Agda formalization of Birkhoff's completeness theorem.
(See: http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf)


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Varieties.Setoid.EquationalLogic {𝑆 : Signature 𝓞 𝓥} where

-- imports from Agda and the Agda Standard Library -------------------------------------------
open import Agda.Primitive   using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type )
open import Data.Product     using ( _,_ ; Σ-syntax ; _×_ ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Function.Base    using ( _∘_ ; flip )
open import Function.Bundles using ( Func )
open import Relation.Binary  using ( Setoid ; IsEquivalence )
open import Relation.Unary   using ( Pred ; _∈_ )
open import Relation.Binary.PropositionalEquality
                             using ( _≡_ ; refl )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open Setoid using ( Carrier ; _≈_ ; isEquivalence )
open Func renaming ( f to _<$>_ )
open IsEquivalence renaming ( refl to reflE ; sym to  symmE ; trans to tranE )


-- imports from agda-algebras --------------------------------------------------------------
open import Overture.Preliminaries       using ( ∣_∣ )
open import Algebras.Setoid.Basic{𝑆 = 𝑆} using ( SetoidAlgebra ) renaming ( ⟦_⟧ to ⟦_⟧s )
open import Algebras.Products    {𝑆 = 𝑆} using ( ov )
open import Terms.Basic          {𝑆 = 𝑆} using ( Term )
open import Terms.Setoid.Basic   {𝑆 = 𝑆} using ( module Environment ; Ops ; Sub ; _[_] )

open Term

private variable
 χ α ρ ℓ : Level
 X Γ Δ : Type χ
 f     : ∣ 𝑆 ∣
 op    : ∣ Ops Γ ∣

-- Equations
-- An equation is a pair (s , t) of terms in the same context.
record Eq : Type (ov χ) where
 constructor _≈̇_
 field
  {cxt} : Type χ
  lhs   : Term cxt
  rhs   : Term cxt

open Eq public


-- Equation p ≈̇ q holding in algebra M. (type \~~\^. to get ≈̇) (type \|= to get ⊨)
_⊨_ : (M : SetoidAlgebra α ℓ)(term-identity : Eq{χ}) → Type _
M ⊨ (p ≈̇ q) = Equal p q  where open Environment M

module _ {ι : Level}{I : Type ι} where

 -- An I-indexed set of equations inhabits the type I → Eq.
 -- For such `E : I → Eq`...

 -- ...`𝑨 ⊧ E` is the assertion that algebra 𝑨 models all equations in a set E.
 _⊧_ : (𝑨 : SetoidAlgebra α ρ)(E : I → Eq{χ}) → Type _
 𝑨 ⊧ E = ∀ i → Equal (lhs (E i))(rhs (E i))       -- (type \models to get ⊧)
  where open Environment 𝑨

 -- ...`Mod E` is the class of algebras that model all term equations in E.
 Mod : (I → Eq{χ}) → Pred(SetoidAlgebra α ρ) (χ ⊔ ι ⊔ α ⊔ ρ)
 Mod E = _⊧ E


_⊫_ : Pred (SetoidAlgebra α ρ) ℓ → Eq{χ} → Type _
𝒦 ⊫ eq = ∀ 𝑨 → 𝒦 𝑨 → 𝑨 ⊨ eq                        -- (type \||= to get ⊫)

module _ {α ρ ℓ χ : Level}{X : Type χ} where

 ThPred : Pred (SetoidAlgebra α ρ) ℓ → Pred(Term X × Term X) (ℓ ⊔ χ ⊔ ov (α ⊔ ρ))
 ThPred 𝒦 = λ (p , q) → 𝒦 ⊫ (p ≈̇ q)

 ℑTh : Pred(Term X × Term X) (ℓ ⊔ χ ⊔ ov (α ⊔ ρ)) → Type (ℓ ⊔ ov (α ⊔ ρ ⊔ χ))
 ℑTh P = Σ[ p ∈ (Term X × Term X) ] p ∈ P

 Th : (𝒦 : Pred (SetoidAlgebra α ρ) ℓ) → ℑTh (ThPred 𝒦) → Eq{χ}
 Th 𝒦 = λ i → fst ∣ i ∣ ≈̇ snd ∣ i ∣

module _ {α}{ρ}{ι}{I : Type ι} where
 -- An entailment E ⊃ eq holds iff it holds in all models of E.
 _⊃_ : (E : I → Eq{χ}) (eq : Eq{χ}) → Type _
 E ⊃ eq = (M : SetoidAlgebra α ρ) → M ⊧ E → M ⊨ eq

\end{code}


#### Derivations in a context

(Based on Andreas Abel's Agda formalization of Birkhoff's completeness theorem;
see: http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf)

\begin{code}

module _ {χ ι : Level} where

 data _⊢_▹_≈_ {I : Type ι}
  (E : I → Eq) : (Γ : Type χ) (p q : Term Γ) → Type ((ov χ) ⊔ ι) where

  hyp : ∀ i → let p ≈̇ q = E i in E ⊢ _ ▹ p ≈ q

  app : ∀ {ps qs} → (∀ i → E ⊢ Γ ▹ ps i ≈ qs i) → E ⊢ Γ ▹ (node f ps) ≈ (node f qs)

  sub : ∀ {p q} → E ⊢ Δ ▹ p ≈ q → ∀ (σ : Sub Γ Δ) → E ⊢ Γ ▹ (p [ σ ]) ≈ (q [ σ ])

  refl : ∀ {p} → E ⊢ Γ ▹ p ≈ p

  sym : ∀ {p q : Term Γ} → E ⊢ Γ ▹ p ≈ q → E ⊢ Γ ▹ q ≈ p

  trans : ∀ {p q r : Term Γ} → E ⊢ Γ ▹ p ≈ q → E ⊢ Γ ▹ q ≈ r → E ⊢ Γ ▹ p ≈ r

\end{code}



#### Soundness of the inference rules

(Based on Andreas Abel's Agda formalization of Birkhoff's completeness theorem;
see: http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf)


\begin{code}

module Soundness {χ α ρ ι : Level}{I : Type ι} (E : I → Eq{χ})
                 (M : SetoidAlgebra α ρ)     -- We assume an algebra M
                 (V : M ⊧ E)         -- that models all equations in E.
                 where
 open SetoidAlgebra M

 -- In any model M that satisfies the equations E, derived equality is actual equality.
 open SetoidReasoning Domain

 open Environment M renaming (⟦_⟧s to ⟪_⟫)
 sound : ∀ {p q} → E ⊢ Γ ▹ p ≈ q → M ⊨ (p ≈̇ q)

 sound (hyp i)                      =  V i
 sound (app {f = f} es) ρ           =  Interp .cong (refl , λ i → sound (es i) ρ)
 sound (sub {p = p} {q} Epq σ) ρ    =  begin
                                       ⟦ p [ σ ] ⟧ <$> ρ          ≈⟨ substitution p σ ρ ⟩
                                       ⟦ p       ⟧ <$> ⟪ σ ⟫ ρ ≈⟨ sound Epq (⟪ σ ⟫ ρ)  ⟩
                                       ⟦ q       ⟧ <$> ⟪ σ ⟫ ρ ≈˘⟨ substitution  q σ ρ ⟩
                                       ⟦ q [ σ ] ⟧ <$> ρ          ∎

 sound (refl {p = p})               = isEquiv .reflE {x = p}
 sound (sym {p = p} {q} Epq)        = isEquiv .symmE {x = p}{q}   (sound Epq)
 sound (trans{p = p}{q}{r} Epq Eqr) = isEquiv .tranE {i = p}{q}{r}(sound Epq)(sound Eqr)


\end{code}

The deductive closure of a set E is the set of equations modeled by all models of E; that is, Th Mod E.

The soundness proof above shows ∀ X → E ⊢ X ▹ p ≈ q → (p , q) ∈ Th Mod ℰ.
That is,  ∀ X → E ⊢ X ▹ p ≈ q → Mod E ⊫ p ≈ q.

The converse is Birkhoff's completeness theorem: if Mod E ⊫ p ≈ q, then E ⊢ X ▹ p ≈ q.

We will prove that result next.

#### Birkhoff's completeness theorem

The proof proceeds by constructing a relatively free algebra consisting of term
quotiented by derivable equality E ⊢ Γ ▹ _≈_.  It then suffices to prove
that this model satisfies all equations in $E$.

(Based on Andreas Abel's Agda formalization of Birkhoff's completeness theorem;
see: http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf)

\begin{code}

-- Universal model
-- A term model for E and Γ is Term Γ modulo E ⊢ Γ ▹ _≈_.
module TermModel {χ : Level}{Γ : Type χ}{ι : Level}{I : Type ι} (E : I → Eq) where
 open SetoidAlgebra

 -- Term Γ modulo E.
 TermSetoid : Type χ → Setoid _ _

 TermSetoid Γ = record { Carrier       = Term Γ
                       ; _≈_           = E ⊢ Γ ▹_≈_
                       ; isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
                       }

 -- The interpretation of an operation is simply the operation itself.
 -- This works since E ⊢ Γ ▹_≈_ is a congruence.
 TermInterp : ∀ {Γ} → Func (⟦ 𝑆 ⟧s (TermSetoid Γ)) (TermSetoid Γ)
 TermInterp <$> (f , ts) = node f ts
 cong TermInterp (refl , h) = app h

 -- The term model per context Γ.
 M : Type χ → SetoidAlgebra _ _
 Domain (M Γ) = TermSetoid Γ
 Interp (M Γ) = TermInterp

 open Environment (M Γ)

 -- The identity substitution σ₀ maps variables to themselves.
 σ₀ : {Γ : Type χ} → Sub Γ Γ
 σ₀ x = ℊ x

 -- σ₀ acts indeed as identity.
 identity : (t : Term Γ) → E ⊢ Γ ▹ t [ σ₀ ] ≈ t
 identity (ℊ x) = refl
 identity (node f ts) = app (identity ∘ ts)

 -- Evaluation in the term model is substitution $E ⊢ Γ ▹ ⟦t⟧σ ≡ t[σ]$.
 -- This would even hold "up to the nose" if we had function extensionality.

 evaluation : (t : Term Δ) (σ : Sub Γ Δ) → E ⊢ Γ ▹ (⟦ t ⟧ <$> σ) ≈ (t [ σ ])
 evaluation (ℊ x)    σ = refl
--  evaluation (node f ts)  σ = app (λ i → evaluation (ts i) σ)
 evaluation (node f ts)  σ = app (flip (evaluation ∘ ts) σ)

 -- The term model satisfies all the equations it started out with.
 satisfies : ∀ i → M Γ ⊨ E i
 satisfies i σ = begin
                 ⟦ p ⟧ <$> σ  ≈⟨ evaluation p σ ⟩
                 p [ σ ]        ≈⟨ sub (hyp i) σ ⟩
                 q [ σ ]        ≈˘⟨ evaluation q σ ⟩
                 ⟦ q ⟧ <$> σ  ∎
                 where
                  open SetoidReasoning (TermSetoid _)
                  p = lhs (E i)
                  q = rhs (E i)

\end{code}

#### Birkhoff's Completeness Theorem

(Based on Andreas Abel's Agda formalization of Birkhoff's completeness theorem;
see: http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf)


\begin{code}

module Completeness {χ ι : Level}{I : Type ι} (E : I → Eq{χ}) {Γ} where
 open TermModel {Γ = Γ} E
 open Environment (M Γ)

 -- Birkhoff's completeness theorem.
 -- Any valid consequence is derivable.
 completeness : ∀ p q → Mod E ⊫ (p ≈̇ q) → E ⊢ Γ ▹ p ≈ q
 completeness p q V = begin
                  p              ≈˘⟨ identity p ⟩
                  p [ σ₀ ]       ≈˘⟨ evaluation p σ₀ ⟩
                  ⟦ p ⟧ <$> σ₀  ≈⟨ V (M Γ) satisfies σ₀ ⟩
                  ⟦ q ⟧ <$> σ₀  ≈⟨ evaluation q σ₀ ⟩
                  q [ σ₀ ]       ≈⟨ identity q ⟩
                  q              ∎
                  where open SetoidReasoning (TermSetoid Γ)


\end{code}






--------------------------------

<br>
<br>

[← Varieties.Setoid](Varieties.Setoid.html)
<span style="float:right;">[Varieties.Setoid.Closure →](Varieties.Setoid.Closure.html)</span>

{% include UALib.Links.md %}


[the agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
