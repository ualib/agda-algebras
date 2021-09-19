---
layout: default
title : "Varieties.Setoid.EquationalLogic module (The Agda Universal Algebra Library)"
date : "2021-01-14"
author: "agda-algebras development team"
---

#### <a id="entailment-derivation-rules-soundness-and-completeness">Entailment, derivation rules, soundness and completeness</a>

This is the [Varieties.Setoid.EquationalLogic][] module of the [Agda Universal Algebra Library][].

This module is based on [Andreas Abel's Agda formalization of Birkhoff's completeness theorem](http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf).

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
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ---------------------------------------------
open import Overture.Preliminaries        using ( ∣_∣ )
open import Algebras.Func.Basic   {𝑆 = 𝑆} using ( SetoidAlgebra ; ov ) renaming ( ⟦_⟧ to ⟦_⟧s )
open import Terms.Basic           {𝑆 = 𝑆} using ( Term )
open import Terms.Func.Basic      {𝑆 = 𝑆} using ( module Environment ; Sub ; _[_] )

open Setoid        using ( Carrier ; _≈_ ; isEquivalence )
open Func          renaming ( f to _⟨$⟩_ )
open Term

private variable
 χ α ρ ℓ : Level
 X Γ Δ : Type χ
 f     : ∣ 𝑆 ∣

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


##### <a id="derivations-in-a-context">Derivations in a context</a>

(Based on [Andreas Abel's Agda formalization of Birkhoff's completeness theorem](http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf).)

\begin{code}

module _ {χ ι : Level} where

 data _⊢_▹_≈_ {I : Type ι}(E : I → Eq) : (X : Type χ)(p q : Term X) → Type (ι ⊔ ov χ) where
  hyp   : ∀ i → let p ≈̇ q = E i in E ⊢ _ ▹ p ≈ q
  app   : ∀ {ps qs} → (∀ i → E ⊢ Γ ▹ ps i ≈ qs i) → E ⊢ Γ ▹ (node f ps) ≈ (node f qs)
  sub   : ∀ {p q} → E ⊢ Δ ▹ p ≈ q → ∀ (σ : Sub Γ Δ) → E ⊢ Γ ▹ (p [ σ ]) ≈ (q [ σ ])

  refl  : ∀ {p}              → E ⊢ Γ ▹ p ≈ p
  sym   : ∀ {p q : Term Γ}   → E ⊢ Γ ▹ p ≈ q → E ⊢ Γ ▹ q ≈ p
  trans : ∀ {p q r : Term Γ} → E ⊢ Γ ▹ p ≈ q → E ⊢ Γ ▹ q ≈ r → E ⊢ Γ ▹ p ≈ r

\end{code}



##### <a id="soundness-of-the-inference-rules">Soundness of the inference rules</a>

(Based on [Andreas Abel's Agda formalization of Birkhoff's completeness theorem](see: http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf).)

\begin{code}

module Soundness {χ α ρ ι : Level}{I : Type ι} (E : I → Eq{χ})
                 (𝑨 : SetoidAlgebra α ρ)     -- We assume an algebra M
                 (V : 𝑨 ⊧ E)         -- that models all equations in E.
                 where
 open SetoidAlgebra 𝑨 using ( Interp ) renaming (Domain to A)

 -- In any model M that satisfies the equations E, derived equality is actual equality.
 open SetoidReasoning A

 open Environment 𝑨 renaming ( ⟦_⟧s to ⟪_⟫ )
 open IsEquivalence renaming ( refl to refl≈ ; sym to  sym≈ ; trans to trans≈ )

 sound : ∀ {p q} → E ⊢ X ▹ p ≈ q → 𝑨 ⊨ (p ≈̇ q)
 sound (hyp i)                      =  V i
 sound (app {f = f} es) ρ           =  Interp .cong (refl , λ i → sound (es i) ρ)
 sound (sub {p = p} {q} Epq σ) ρ    =  begin
                                       ⟦ p [ σ ] ⟧ ⟨$⟩ ρ       ≈⟨ substitution p σ ρ ⟩
                                       ⟦ p       ⟧ ⟨$⟩ ⟪ σ ⟫ ρ ≈⟨ sound Epq (⟪ σ ⟫ ρ)  ⟩
                                       ⟦ q       ⟧ ⟨$⟩ ⟪ σ ⟫ ρ ≈˘⟨ substitution  q σ ρ ⟩
                                       ⟦ q [ σ ] ⟧ ⟨$⟩ ρ       ∎

 sound (refl {p = p})               = refl≈  isEquiv {x = p}
 sound (sym {p = p} {q} Epq)        = sym≈   isEquiv {x = p}{q}   (sound Epq)
 sound (trans{p = p}{q}{r} Epq Eqr) = trans≈ isEquiv {i = p}{q}{r}(sound Epq)(sound Eqr)

\end{code}

The deductive closure of a set E is the set of equations modeled by all models of E; that is, Th Mod E.

The soundness proof above shows ∀ X → E ⊢ X ▹ p ≈ q → (p , q) ∈ Th Mod ℰ.
That is,  ∀ X → E ⊢ X ▹ p ≈ q → Mod E ⊫ p ≈ q.

The converse is Birkhoff's completeness theorem: if Mod E ⊫ p ≈ q, then E ⊢ X ▹ p ≈ q.

We will prove that result next.



##### <a id="birkhoffs-completeness-theorem">Birkhoff's completeness theorem</a>

The proof proceeds by constructing a relatively free algebra consisting of term
quotiented by derivable equality E ⊢ X ▹ _≈_.  It then suffices to prove
that this model satisfies all equations in $E$.

(Based on [Andreas Abel's Agda formalization of Birkhoff's completeness theorem](http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf).)

We denote by `𝔽[ X ]` the *relatively free algebra* over `X` (relative to `E`), which is defined as `Term X` modulo `E ⊢ X ▹ _≈_`.  This algebra `𝔽[ X ]` is "free" or "initial" in the variety of algebras satisfying the identities in `E` in the sense that it satisfies the following universal property: for each algebra `𝑨`, if `𝑨 ⊧ E`, then there is a unique homomorphism from `𝔽[ X ]` to `𝑨`.

\begin{code}

module FreeAlgebra {χ : Level}{X : Type χ}{ι : Level}{I : Type ι}(E : I → Eq) where
 open SetoidAlgebra

 -- Domain of the relatively free algebra.
 FreeDomain : Type χ → Setoid _ _
 FreeDomain X = record { Carrier       = Term X
                       ; _≈_           = E ⊢ X ▹_≈_
                       ; isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
                       }

 -- The interpretation of an operation is simply the operation itself.
 -- This works since E ⊢ X ▹_≈_ is a congruence.
 FreeInterp : ∀ {X} → Func (⟦ 𝑆 ⟧s (FreeDomain X)) (FreeDomain X)
 FreeInterp ⟨$⟩ (f , ts) = node f ts
 cong FreeInterp (refl , h) = app h


 -- The relatively free algebra
 𝔽[_] : Type χ → SetoidAlgebra _ _
 Domain 𝔽[ X ] = FreeDomain X
 Interp 𝔽[ X ] = FreeInterp

 open Environment 𝔽[ X ]
 open SetoidAlgebra 𝔽[ X ] using ( Interp ) renaming ( Domain to 𝔽 )

 -- The identity substitution σ₀ maps variables to themselves.
 σ₀ : {X : Type χ} → Sub X X
 σ₀ x = ℊ x

 -- σ₀ acts indeed as identity.
 identity : (t : Term X) → E ⊢ X ▹ t [ σ₀ ] ≈ t
 identity (ℊ x) = refl
 identity (node f ts) = app (identity ∘ ts)

\end{code}

Evaluation in the term model is substitution `E ⊢ X ▹ ⟦t⟧σ ≈ t[σ]`. (This would
hold "on the nose" if we had function extensionality.)

\begin{code}

 evaluation : (t : Term Δ) (σ : Sub X Δ) → E ⊢ X ▹ (⟦ t ⟧ ⟨$⟩ σ) ≈ (t [ σ ])
 evaluation (ℊ x)    σ = refl
 evaluation (node f ts)  σ = app (flip (evaluation ∘ ts) σ)

 -- The term model satisfies all the equations it started out with.
 satisfies : ∀ i → 𝔽[ X ] ⊨ E i
 satisfies i σ = begin
                 ⟦ p ⟧ ⟨$⟩ σ  ≈⟨ evaluation p σ ⟩
                 p [ σ ]        ≈⟨ sub (hyp i) σ ⟩
                 q [ σ ]        ≈˘⟨ evaluation q σ ⟩
                 ⟦ q ⟧ ⟨$⟩ σ  ∎
                 where
                  open SetoidReasoning 𝔽
                  p = lhs (E i)
                  q = rhs (E i)

\end{code}

We are finally ready to formally state and prove Birkhoff's Completeness Theorem, which asserts that every valid consequence is derivable.

\begin{code}

 completeness : ∀ p q → Mod E ⊫ (p ≈̇ q) → E ⊢ X ▹ p ≈ q
 completeness p q V = begin
       p              ≈˘⟨ identity p ⟩
       p [ σ₀ ]       ≈˘⟨ evaluation p σ₀ ⟩
       ⟦ p ⟧ ⟨$⟩ σ₀   ≈⟨ V 𝔽[ X ] satisfies σ₀ ⟩
       ⟦ q ⟧ ⟨$⟩ σ₀   ≈⟨ evaluation q σ₀ ⟩
       q [ σ₀ ]       ≈⟨ identity q ⟩
       q              ∎
  where open SetoidReasoning 𝔽
\end{code}

--------------------------------

<span style="float:left;">[↑ Varieties.Setoid](Varieties.Setoid.html)</span>
<span style="float:right;">[Varieties.Setoid.Closure →](Varieties.Setoid.Closure.html)</span>

{% include UALib.Links.md %}
