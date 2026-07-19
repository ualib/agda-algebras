---
layout: default
title : "Setoid.Varieties.SoundAndComplete module (The Agda Universal Algebra Library)"
date : "2021-01-14"
author: "agda-algebras development team"
---

#### Entailment, derivation rules, soundness and completeness

This is the [Setoid.Varieties.SoundAndComplete][] module of the [Agda Universal Algebra Library][].

This module is based on [Andreas Abel's Agda formalization of Birkhoff's completeness theorem](http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf).

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature ; 𝑆)

module Setoid.Varieties.SoundAndComplete where

open import Agda.Primitive   using () renaming ( Set to Type )

-- imports from the Agda Standard Library ---------------------------------------
open import Data.Product     using ( _,_ ; Σ-syntax ; _×_ )
open import Function         using ( _∘_ ; flip ) renaming ( Func to _⟶_ )
open import Level            using ( Level ; _⊔_ )
open import Relation.Binary  using ( Setoid ; IsEquivalence )
open import Relation.Unary   using ( Pred ; _∈_ )

open import Relation.Binary.PropositionalEquality using ( refl )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library -------------------------------
open import Overture                  using ( proj₁ ; proj₂ ; OperationSymbolsOf )
open import Overture.Terms  using ( Term )
open import Setoid.Algebras  using ( Algebra ; ov ; 𝔻[_] )
open import Setoid.Signatures         using ( ⟨_⟩ )
open import Setoid.Terms  using ( module Environment ; Sub ; _[_] )

open Setoid  using ( Carrier ; _≈_ ; isEquivalence )
open _⟶_     renaming ( to to _⟨$⟩_ )
open Term

private variable
  χ α ρᵃ ι ℓ : Level
  X Γ Δ : Type χ
  f : OperationSymbolsOf 𝑆
  I : Type ι
```
-->

```agda
-- Equations
-- An equation is a pair (s , t) of terms in the same context.
record Eq {χ : Level} : Type (ov {𝑆 = 𝑆} χ) where
  constructor _≈̇_
  field
    {cxt}  : Type χ
    lhs    : Term {𝑆 = 𝑆} cxt
    rhs    : Term {𝑆 = 𝑆} cxt
infix 6 _≈̇_
open Eq public

-- The "impedance shim" between the library's two theory shapes.  The interpretability
-- machinery (Setoid.Varieties.Interpretation) records a theory as an indexed family of
-- *pairs of terms* (Idx → Term X × Term X); the derivation calculus _⊢_▹_≈_ and the
-- free algebra 𝔽[_] below consume an indexed family of *equations* (I → Eq).  toEq
-- converts the former to the latter.  No companion is needed for satisfaction: 𝑨 ⊨ₑ ℰ
-- there and 𝑨 ⊨ toEq ℰ below coincide definitionally (both unfold to pointwise
-- equality of the two interpreted terms under all environments).
toEq : {χ ι : Level}{Idx : Type ι}{X : Type χ}
  → (Idx → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X) → (Idx → Eq {χ = χ})
toEq ℰ i = proj₁ (ℰ i) ≈̇ proj₂ (ℰ i)

-- Equation p ≈̇ q holding in algebra M. (type \~~\^. to get ≈̇; type \models to get ⊧)
_⊧_ : (𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ)(term-identity : Eq {χ = χ}) → Type _
𝑨 ⊧ (p ≈̇ q) = Equal p q where open Environment 𝑨

-- 𝒦 ⊫ (p ≈̇ q) asserts that every algebra in the class 𝒦 models the equation
-- p ≈̇ q.  This is a one-field record (a frozen wrapper around the underlying
-- ∀ 𝑨 → 𝒦 𝑨 → 𝑨 ⊧ eq) rather than a plain function type, so that the equation
-- stays visible as an Eq during unification.  Inferring the implicit {p}{q} of
-- a preservation lemma such as V-id1 then unifies the two equations
-- structurally at the Eq level — the record type former _⊫_ is injective —
-- instead of unfolding _⊫_ → _⊧_ → Equal → ⟦_⟧ and getting stuck on the term
-- interpreter.  (See issue #361.  Note _⊧_ and Equal still reduce
-- definitionally, so the proofs that compute with them are unaffected.)
record _⊫_ (𝒦 : Pred (Algebra {𝑆 = 𝑆} α ρᵃ) ℓ)(eq : Eq {χ = χ}) : Type (ℓ ⊔ χ ⊔ ov {𝑆 = 𝑆}(α ⊔ ρᵃ)) where
  constructor ⊫-intro
  field ⊫-proof : ∀ (𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ) → 𝒦 𝑨 → 𝑨 ⊧ eq          -- (type \||= to get ⊫)
open _⊫_ public
infix 5 _⊫_

-- An I-indexed set of equations inhabits the type I → Eq.

-- For such `ℰ : I → Eq`...

-- ...`𝑨 ⊨ ℰ` is the assertion that the algebra 𝑨 models every equation in ℰ.
_⊨_ : (𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ) → (I → Eq {χ = χ}) → Type _
𝑨 ⊨ ℰ = ∀ i → Equal (lhs (ℰ i))(rhs (ℰ i)) where open Environment 𝑨  --   (type \|= to get ⊨)

-- ...`𝒦 ∥≈ ℰ` is the assertion that every algebra in 𝒦 models every equation in ℰ.
_∥≈_ : Pred (Algebra {𝑆 = 𝑆} α ρᵃ) ℓ → (I → Eq {χ = χ}) → Type _
𝒦 ∥≈ ℰ = ∀ i → 𝒦 ⊫ ℰ i

-- ...`Mod ℰ` is the class of algebras that model every equation in ℰ.
ModTuple : (I → Eq {χ = χ}) → Pred(Algebra {𝑆 = 𝑆} α ρᵃ) _
ModTuple ℰ = _⊨ ℰ

module _ {α ρᵃ ℓ χ : Level} {X : Type χ} where

  Mod : Pred(Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X) ℓ → Pred (Algebra {𝑆 = 𝑆} α ρᵃ) _
  Mod ℰ 𝑨 = ∀ {p q} → (p , q) ∈ ℰ → Equal p q
    where open Environment 𝑨

  Th : Pred (Algebra {𝑆 = 𝑆} α ρᵃ) ℓ → Pred(Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X) _
  Th 𝒦 = λ (p , q) → 𝒦 ⊫ (p ≈̇ q)

  ℑTh : Pred(Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X) (ℓ ⊔ χ ⊔ ov {𝑆 = 𝑆} (α ⊔ ρᵃ)) → Type _
  ℑTh P = Σ[ p ∈ (Term _ × Term _) ] p ∈ P

  ThTuple : (𝒦 : Pred (Algebra {𝑆 = 𝑆} α ρᵃ) ℓ) → ℑTh (Th 𝒦) → Eq {χ = χ}
  ThTuple 𝒦 = λ i → proj₁ (proj₁ i) ≈̇ proj₂ (proj₁ i)

module _ {𝑆 : Signature 𝓞 𝓥}{α}{ρᵃ}{ι}{I : Type ι} where
  -- An entailment E ⊃ eq holds iff it holds in all models of E.
  _⊃_ : (E : I → Eq {𝑆 = 𝑆}{χ = χ}) (eq : Eq {𝑆 = 𝑆}{χ = χ}) → Type _
  E ⊃ eq = (M : Algebra {𝑆 = 𝑆} α ρᵃ) → M ⊨ E → M ⊧ eq
```

##### Derivations in a context

```agda
module _ {𝑆 : Signature 𝓞 𝓥}{χ ι : Level} where

  data _⊢_▹_≈_ {I : Type ι}(E : I → Eq) : (X : Type χ)(p q : Term {𝑆 = 𝑆} X) → Type (ι ⊔ ov {𝑆 = 𝑆} χ) where
    hyp    : ∀ (i : I)           → let p ≈̇ q = E i in E ⊢ _ ▹ p ≈ q
    app    : ∀ {f : OperationSymbolsOf 𝑆}{ps qs}  → (∀ i → E ⊢ Γ ▹ ps i ≈ qs i) → E ⊢ Γ ▹ node f ps ≈ node f qs
    sub    : ∀ {p q : Term {𝑆 = 𝑆} Δ}    → E ⊢ Δ ▹ p ≈ q → ∀ (σ : Sub {𝑆 = 𝑆} Γ Δ) → E ⊢ Γ ▹ p [ σ ] ≈ q [ σ ]
    refl   : ∀ {p : Term {𝑆 = 𝑆} Γ}      → E ⊢ Γ ▹ p ≈ p
    sym    : ∀ {p q : Term {𝑆 = 𝑆} Γ}    → E ⊢ Γ ▹ p ≈ q → E ⊢ Γ ▹ q ≈ p
    trans  : ∀ {p q r : Term {𝑆 = 𝑆} Γ}  → E ⊢ Γ ▹ p ≈ q → E ⊢ Γ ▹ q ≈ r → E ⊢ Γ ▹ p ≈ r
  infix 4 _⊢_▹_≈_

  ⊢▹≈IsEquiv : {I : Type ι}{E : I → Eq} → IsEquivalence (E ⊢ Γ ▹_≈_)
  ⊢▹≈IsEquiv = record { refl = refl ; sym = sym ; trans = trans }
```

##### Soundness of the inference rules

```agda
module Soundness
  {χ α ι : Level}{I : Type ι} (E : I → Eq {χ = χ})
  (𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ)   -- We assume an algebra 𝑨
  (V : 𝑨 ⊨ E)          -- that models all equations in E.
  where
  open Algebra 𝑨 using ( Interp ) --  renaming (Domain to A)

  -- In any model 𝑨 that satisfies the equations E, derived equality is actual equality.
  open SetoidReasoning 𝔻[ 𝑨 ]
  open Environment 𝑨 renaming ( ⟦_⟧s to ⟪_⟫ )
  open IsEquivalence renaming ( refl to refl≈ ; sym to  sym≈ ; trans to trans≈ )

  sound : ∀ {p q} → E ⊢ X ▹ p ≈ q → 𝑨 ⊧ (p ≈̇ q)
  sound (hyp i)                    = V i
  sound (app {f = f} es) ρ         = Interp .cong (refl , λ i → sound (es i) ρ)
  sound (sub {p = p} {q} Epq σ) ρ  = begin
    ⟦ p [ σ ] ⟧ ⟨$⟩        ρ  ≈⟨ substitution p σ ρ ⟩
    ⟦ p       ⟧ ⟨$⟩ ⟪ σ ⟫  ρ  ≈⟨ sound Epq (⟪ σ ⟫ ρ)  ⟩
    ⟦ q       ⟧ ⟨$⟩ ⟪ σ ⟫  ρ  ≈˘⟨ substitution  q σ ρ ⟩
    ⟦ q [ σ ] ⟧ ⟨$⟩        ρ  ∎

  sound (refl {p = p})                = refl≈   isEquiv {x = p}
  sound (sym {p = p} {q} Epq)         = sym≈    isEquiv {x = p}{q}     (sound Epq)
  sound (trans{p = p}{q}{r} Epq Eqr)  = trans≈  isEquiv {i = p}{q}{r}  (sound Epq)(sound Eqr)
```

The deductive closure of a set E is the set of equations modeled by all models of E;
that is, `Th Mod E`.

The soundness proof above shows

    ∀ X → E ⊢ X ▹ p ≈ q → (p , q) ∈ Th Mod ℰ.

That is, `∀ X → E ⊢ X ▹ p ≈ q → Mod E ⊫ p ≈ q`.

The converse is Birkhoff's completeness theorem:
if `Mod E ⊫ p ≈ q`, then `E ⊢ X ▹ p ≈ q`.

We will prove that result next.


##### Birkhoff's completeness theorem

The proof proceeds by constructing a relatively free algebra consisting of term
quotiented by derivable equality `E ⊢ X ▹ _≈_`.  It then suffices to prove that this
model satisfies all equations in `E`.

We denote by `𝔽[ X ]` the *relatively free algebra* over `X` (relative to `E`), which
is defined as `Term X` modulo `E ⊢ X ▹ _≈_`.  This algebra `𝔽[ X ]` is "free" or
"initial" in the variety of algebras satisfying the identities in `E` in the sense
that it satisfies the following universal property: for each algebra `𝑨`, if `𝑨 ⊧ E`,
then there is a unique homomorphism from `𝔽[ X ]` to `𝑨`.

```agda
module FreeAlgebra {𝑆 : Signature 𝓞 𝓥}{χ : Level}{ι : Level}{I : Type ι}(E : I → Eq {χ = χ}) where
  open Algebra

  -- Domain of the relatively free algebra.
  FreeDomain : Type χ → Setoid _ _
  FreeDomain X = record  { Carrier        = Term X
                         ; _≈_            = E ⊢ X ▹_≈_
                         ; isEquivalence  = ⊢▹≈IsEquiv
                         }

  -- The interpretation of an operation is simply the operation itself.
  -- This works since E ⊢ X ▹_≈_ is a congruence.
  FreeInterp : ∀ {X} → (⟨ 𝑆 ⟩ (FreeDomain X)) ⟶ (FreeDomain X)
  FreeInterp ⟨$⟩ (f , ts) = node f ts
  FreeInterp .cong (refl , h) = app h

  -- The relatively free algebra
  𝔽[_] : Type χ → Algebra {𝑆 = 𝑆} (ov {𝑆 = 𝑆} χ) (ι ⊔ ov {𝑆 = 𝑆} χ)
  Domain 𝔽[ X ] = FreeDomain X
  Interp 𝔽[ X ] = FreeInterp

  -- The identity substitution σ₀ maps variables to themselves.
  σ₀ : {X : Type χ} → Sub {𝑆 = 𝑆} X X
  σ₀ x = ℊ x

  -- σ₀ acts indeed as identity.
  identity : (t : Term {𝑆 = 𝑆} X) → E ⊢ X ▹ t [ σ₀ ] ≈ t
  identity (ℊ x) = refl
  identity (node f ts) = app (identity ∘ ts)
```

Evaluation in the term model is substitution `E ⊢ X ▹ ⟦t⟧σ ≈ t[σ]`. (This would
hold "on the nose" if we had function extensionality.)

(We put this and the next two lemmas into their own submodules to emphasize
the fact that these results are independent of the chosen variable symbol
type `X` (or `Δ`, or `Γ`), which is an arbitrary inhabitant of `Type χ`.)

```agda
  module _ {X : Type χ} where
    open Environment 𝔽[ X ]
    evaluation : (t : Term {𝑆 = 𝑆} Δ) (σ : Sub {𝑆 = 𝑆} X Δ) → E ⊢ X ▹ (⟦ t ⟧ ⟨$⟩ σ) ≈ (t [ σ ])
    evaluation (ℊ x) σ = refl
    evaluation (node f ts) σ = app (flip (evaluation ∘ ts) σ)

  module _ {Δ : Type χ} where
    -- The term model satisfies all the equations it started out with.
    satisfies : 𝔽[ Δ ] ⊨ E
    satisfies i σ = begin
      ⟦ p ⟧ ⟨$⟩ σ  ≈⟨ evaluation p σ ⟩
      p [ σ ]      ≈⟨ sub (hyp i) σ ⟩
      q [ σ ]      ≈˘⟨ evaluation q σ ⟩
      ⟦ q ⟧ ⟨$⟩ σ  ∎
      where
      open Environment 𝔽[ Δ ]
      open SetoidReasoning (Domain 𝔽[ Δ ]) ; p = lhs (E i) ; q = rhs (E i)
```

We are finally ready to formally state and prove Birkhoff's Completeness Theorem,
which asserts that every valid consequence is derivable.

```agda
  module _ {Γ : Type χ} where

    completeness : ∀ p q → ModTuple E ⊫ (p ≈̇ q) → E ⊢ Γ ▹ p ≈ q
    completeness p q V = begin
      p              ≈˘⟨ identity p ⟩
      p [ σ₀ ]       ≈˘⟨ evaluation p σ₀ ⟩
      ⟦ p ⟧ ⟨$⟩ σ₀   ≈⟨ V .⊫-proof 𝔽[ Γ ] satisfies σ₀ ⟩
      ⟦ q ⟧ ⟨$⟩ σ₀   ≈⟨ evaluation q σ₀ ⟩
      q [ σ₀ ]       ≈⟨ identity q ⟩
      q              ∎
      where
      open Environment 𝔽[ Γ ]
      open SetoidReasoning (Domain 𝔽[ Γ ])
```
