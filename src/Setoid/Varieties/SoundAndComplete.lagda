---
layout: default
title : "Setoid.Varieties.SoundAndComplete module (The Agda Universal Algebra Library)"
date : "2021-01-14"
author: "agda-algebras development team"
---

#### <a id="entailment-derivation-rules-soundness-and-completeness">Entailment, derivation rules, soundness and completeness</a>

This is the [Setoid.Varieties.SoundAndComplete][] module of the [Agda Universal Algebra Library][].

This module is based on [Andreas Abel's Agda formalization of Birkhoff's completeness theorem](http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Base.Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Varieties.SoundAndComplete {𝑆 : Signature 𝓞 𝓥} where

-- imports from Agda and the Agda Standard Library -------------------------------------------
open import Agda.Primitive   using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type )
open import Data.Product     using ( _,_ ; Σ-syntax ; _×_ ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Function.Base    using ( _∘_ ; flip ; id )
open import Function.Bundles using () renaming ( Func to _⟶_ )
open import Relation.Binary  using ( Setoid ; IsEquivalence )
open import Relation.Unary   using ( Pred ; _∈_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ---------------------------------------------
open import Base.Overture.Preliminaries     using ( ∣_∣ )
open import Base.Terms.Basic       {𝑆 = 𝑆}  using ( Term )
open import Setoid.Algebras.Basic  {𝑆 = 𝑆}  using ( Algebra ; ov ; ⟨_⟩ )
open import Setoid.Terms.Basic     {𝑆 = 𝑆}  using ( module Environment ; Sub ; _[_] )

open Setoid  using ( Carrier ; _≈_ ; isEquivalence )
open _⟶_     renaming ( f to _⟨$⟩_ )
open Term

private variable
 χ α ρᵃ ι ℓ : Level
 X Γ Δ : Type χ
 f     : ∣ 𝑆 ∣
 I : Type ι

-- Equations
-- An equation is a pair (s , t) of terms in the same context.
record Eq : Type (ov χ) where
 constructor _≈̇_
 field
  {cxt} : Type χ
  lhs   : Term cxt
  rhs   : Term cxt

open Eq public

-- Equation p ≈̇ q holding in algebra M. (type \~~\^. to get ≈̇; type \models to get ⊧)
_⊧_ : (𝑨 : Algebra α ρᵃ)(term-identity : Eq{χ}) → Type _
𝑨 ⊧ (p ≈̇ q) = Equal p q where open Environment 𝑨

_⊫_ : Pred (Algebra α ρᵃ) ℓ → Eq{χ} → Type (ℓ ⊔ χ ⊔ ov(α ⊔ ρᵃ))
𝒦 ⊫ eq = ∀ 𝑨 → 𝒦 𝑨 → 𝑨 ⊧ eq                    -- (type \||= to get ⊫)

-- An I-indexed set of equations inhabits the type I → Eq.

-- For such `ℰ : I → Eq`...

-- ...`𝑨 ⊨ ℰ` is the assertion that the algebra 𝑨 models every equation in ℰ.
_⊨_ : (𝑨 : Algebra α ρᵃ) → (I → Eq{χ}) → Type _
𝑨 ⊨ ℰ = ∀ i → Equal (lhs (ℰ i))(rhs (ℰ i)) where open Environment 𝑨  --   (type \|= to get ⊨)

-- ...`𝒦 ∥≈ ℰ` is the assertion that every algebra in 𝒦 models every equation in ℰ.
_∥≈_ : Pred (Algebra α ρᵃ) ℓ → (I → Eq{χ}) → Type _
𝒦 ∥≈ ℰ = ∀ i → 𝒦 ⊫ ℰ i

-- ...`Mod ℰ` is the class of algebras that model every equation in ℰ.
ModTuple : (I → Eq{χ}) → Pred(Algebra α ρᵃ) _
ModTuple ℰ = _⊨ ℰ

module _ {α ρᵃ ℓ : Level} where

 Mod : Pred(Term X × Term X) ℓ → Pred (Algebra α ρᵃ) _ -- (𝓞 ⊔ 𝓥 ⊔ lsuc χ ⊔ ℓ ⊔ α ⊔ ρᵃ)
 Mod ℰ 𝑨 = ∀ {p q} → (p , q) ∈ ℰ → Equal p q where open Environment 𝑨

 Th : Pred (Algebra α ρᵃ) ℓ → Pred(Term X × Term X) _ -- (ℓ ⊔ χ ⊔ ov (α ⊔ ρᵃ))
 Th 𝒦 = λ (p , q) → 𝒦 ⊫ (p ≈̇ q)

 ℑTh : Pred(Term X × Term X) (ℓ ⊔ χ ⊔ ov (α ⊔ ρᵃ)) → Type _ -- (ℓ ⊔ ov (α ⊔ ρᵃ ⊔ χ))
 ℑTh P = Σ[ p ∈ (Term _ × Term _) ] p ∈ P

 module _ {χ : Level}{X : Type χ} where

  ThTuple : (𝒦 : Pred (Algebra α ρᵃ) ℓ) → ℑTh{χ = χ} (Th{X = X} 𝒦) → Eq{χ}
  ThTuple 𝒦 = λ i → fst ∣ i ∣ ≈̇ snd ∣ i ∣

module _ {α}{ρᵃ}{ι}{I : Type ι} where
 -- An entailment E ⊃ eq holds iff it holds in all models of E.
 _⊃_ : (E : I → Eq{χ}) (eq : Eq{χ}) → Type _
 E ⊃ eq = (M : Algebra α ρᵃ) → M ⊨ E → M ⊧ eq

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

 ⊢▹≈IsEquiv : {I : Type ι}{E : I → Eq} → IsEquivalence (E ⊢ Γ ▹_≈_)
 ⊢▹≈IsEquiv = record { refl = refl ; sym = sym ; trans = trans }

\end{code}



##### <a id="soundness-of-the-inference-rules">Soundness of the inference rules</a>

(Based on [Andreas Abel's Agda formalization of Birkhoff's completeness theorem](see: http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf).)

\begin{code}

module Soundness {χ α ι : Level}{I : Type ι} (E : I → Eq{χ})
                 (𝑨 : Algebra α ρᵃ)     -- We assume an algebra M
                 (V : 𝑨 ⊨ E)         -- that models all equations in E.
                 where
 open Algebra 𝑨 using ( Interp ) renaming (Domain to A)

 -- In any model M that satisfies the equations E, derived equality is actual equality.
 open SetoidReasoning A

 open Environment 𝑨 renaming ( ⟦_⟧s to ⟪_⟫ )
 open IsEquivalence renaming ( refl to refl≈ ; sym to  sym≈ ; trans to trans≈ )

 sound : ∀ {p q} → E ⊢ X ▹ p ≈ q → 𝑨 ⊧ (p ≈̇ q)
 sound (hyp i)                      = V i
 sound (app {f = f} es) ρ           = Interp .cong (refl , λ i → sound (es i) ρ)
 sound (sub {p = p} {q} Epq σ) ρ    =
  begin
   ⟦ p [ σ ] ⟧ ⟨$⟩       ρ ≈⟨ substitution p σ ρ ⟩
   ⟦ p       ⟧ ⟨$⟩ ⟪ σ ⟫ ρ ≈⟨ sound Epq (⟪ σ ⟫ ρ)  ⟩
   ⟦ q       ⟧ ⟨$⟩ ⟪ σ ⟫ ρ ≈˘⟨ substitution  q σ ρ ⟩
   ⟦ q [ σ ] ⟧ ⟨$⟩       ρ ∎

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

module FreeAlgebra {χ : Level}{ι : Level}{I : Type ι}(E : I → Eq) where
 open Algebra

 -- Domain of the relatively free algebra.
 FreeDomain : Type χ → Setoid _ _
 FreeDomain X = record { Carrier       = Term X
                       ; _≈_           = E ⊢ X ▹_≈_
                       ; isEquivalence = ⊢▹≈IsEquiv
                       }

 -- The interpretation of an operation is simply the operation itself.
 -- This works since E ⊢ X ▹_≈_ is a congruence.
 FreeInterp : ∀ {X} → (⟨ 𝑆 ⟩ (FreeDomain X)) ⟶ (FreeDomain X)
 FreeInterp ⟨$⟩ (f , ts) = node f ts
 cong FreeInterp (refl , h) = app h


 -- The relatively free algebra
 𝔽[_] : Type χ → Algebra (ov χ) (ι ⊔ ov χ)
 Domain 𝔽[ X ] = FreeDomain X
 Interp 𝔽[ X ] = FreeInterp


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

(We put this and the next two lemmas into their own submodules to emphasize
the fact that these results are independent of the chosen variable symbol
type `X` (or `Δ`, or `Γ`), which is an arbitrary inhabitant of `Type χ`.)
\begin{code}

 module _ {X : Type χ} where
  open Environment 𝔽[ X ]
  evaluation : (t : Term Δ) (σ : Sub X Δ) → E ⊢ X ▹ (⟦ t ⟧ ⟨$⟩ σ) ≈ (t [ σ ])
  evaluation (ℊ x) σ = refl
  evaluation (node f ts) σ = app (flip (evaluation ∘ ts) σ)


 module _ {Δ : Type χ} where
  -- The term model satisfies all the equations it started out with.
  satisfies : 𝔽[ Δ ] ⊨ E
  satisfies i σ =
   begin
    ⟦ p ⟧ ⟨$⟩ σ  ≈⟨ evaluation p σ ⟩
    p [ σ ]      ≈⟨ sub (hyp i) σ ⟩
    q [ σ ]      ≈˘⟨ evaluation q σ ⟩
    ⟦ q ⟧ ⟨$⟩ σ  ∎
    where
    open Environment 𝔽[ Δ ]
    open SetoidReasoning (Domain 𝔽[ Δ ]) ; p = lhs (E i) ; q = rhs (E i)

\end{code}

We are finally ready to formally state and prove Birkhoff's Completeness Theorem, which asserts that every valid consequence is derivable.

\begin{code}

 module _ {Γ : Type χ} where

  completeness : ∀ p q → ModTuple E ⊫ (p ≈̇ q) → E ⊢ Γ ▹ p ≈ q
  completeness p q V =
   begin
    p              ≈˘⟨ identity p ⟩
    p [ σ₀ ]       ≈˘⟨ evaluation p σ₀ ⟩
    ⟦ p ⟧ ⟨$⟩ σ₀   ≈⟨ V 𝔽[ Γ ] satisfies σ₀ ⟩
    ⟦ q ⟧ ⟨$⟩ σ₀   ≈⟨ evaluation q σ₀ ⟩
    q [ σ₀ ]       ≈⟨ identity q ⟩
    q              ∎
   where
   open Environment 𝔽[ Γ ]
   open SetoidReasoning (Domain 𝔽[ Γ ])

\end{code}

--------------------------------

<span style="float:left;">[↑ Setoid.Varieties](Setoid.Varieties.html)</span>
<span style="float:right;">[Setoid.Varieties.Closure →](Setoid.Varieties.Closure.html)</span>

{% include UALib.Links.md %}
