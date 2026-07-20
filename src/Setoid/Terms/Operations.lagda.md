---
layout: default
title : "Setoid.Terms.Operations module (The Agda Universal Algebra Library)"
date : "2021-09-25"
author: "agda-algebras development team"
---

#### Term Operations for Setoid Algebras

This section presents the [Setoid.Terms.Operations][] module of the [Agda Universal Algebra Library][].

Here we define *term operations* which are simply terms interpreted in a particular algebra, and we prove some compatibility properties of term operations.


<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Terms.Operations where

-- Imports from Agda and the Agda Standard Library ---------------------
open import Agda.Primitive    using ()  renaming ( Set to Type )
open import Data.Product      using ( _,_ )
open import Function.Base     using ( _∘_ )
open import Function.Bundles  using ()         renaming ( Func to _⟶_ )
open import Level             using ( Level )
open import Relation.Binary   using ( Setoid )

open import Relation.Binary.PropositionalEquality as ≡ using ( _≡_ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from Agda Universal Algebra Library -----------------------------------
open  import Overture                         using ( proj₁ ; proj₂ ; OperationSymbolsOf ; ArityOf ; 𝓞 ; 𝓥 ; Signature ; 𝑆 )
open  import Overture.Terms using ( Term )
open  import Setoid.Algebras using ( Algebra ; _^_ ; ov ; ⨅ )
open  import Setoid.Homomorphisms using ( hom ; IsHom )
open  import Setoid.Terms.Properties using ( free-lift )
open  import Setoid.Terms.Basic
      using ( module Environment ; 𝑻 ; _≐_ ; ≐-isRefl )

open Term
open _⟶_ using ( cong ) renaming ( to to _⟨$⟩_ )

private variable
  α ρᵃ β ρᵇ ρ χ ι : Level
  X : Type χ
```
-->


It turns out that the intepretation of a term is the same as the `free-lift`
(modulo argument order and assuming function extensionality).


```agda
module _ {𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ} where
  open Algebra 𝑨      using ( Interp )      renaming (Domain to A )
  open Setoid A       using ( _≈_ ; refl )  renaming ( Carrier to ∣A∣ )
  open Environment 𝑨  using ( ⟦_⟧ )

  free-lift-interp :  (η : X → ∣A∣)(p : Term {𝑆 = 𝑆} X)
    → ⟦ p ⟧ ⟨$⟩ η ≈ (free-lift{𝑨 = 𝑨} η) p

  free-lift-interp η (ℊ x) = refl
  free-lift-interp η (node f t) = cong Interp (≡.refl , (free-lift-interp η) ∘ t)

module _ {𝑆 : Signature 𝓞 𝓥}{X : Type χ} where
  open Algebra (𝑻 {𝑆 = 𝑆} X)      using ( Interp ) renaming (Domain to TX )
  open Setoid TX          using ( _≈_ ; refl )
  open Environment (𝑻 {𝑆 = 𝑆} X)  using ( ⟦_⟧ ; ≐→Equal )
  open SetoidReasoning TX

  term-interp :  (f : OperationSymbolsOf 𝑆){s t : ArityOf 𝑆 f → Term {𝑆 = 𝑆} X} → (∀ i → s i ≐ t i)
   → ∀ η → ⟦ node f s ⟧ ⟨$⟩ η ≈ ⟦ node f t ⟧ ⟨$⟩ η

  term-interp f {s}{t} st η = cong Interp (≡.refl , λ i → ≐→Equal (s i) (t i) (st i) η )

  term-agreement : (p : Term {𝑆 = 𝑆} X) → p ≈ ⟦ p ⟧ ⟨$⟩ ℊ
  term-agreement (ℊ x) = refl
  term-agreement (node f t) = cong Interp (≡.refl , (λ i → term-agreement (t i)))
```

#### Interpretation of terms in product algebras

```agda
module _ {X : Type χ }{I : Type ι}(𝒜 : I → Algebra {𝑆 = 𝑆} α ρᵃ) where
  open Algebra (⨅ 𝒜)      using (Interp)  renaming ( Domain to ⨅A )
  open Setoid ⨅A          using ( _≈_ ; refl )
  open Environment (⨅ 𝒜)  using ()        renaming ( ⟦_⟧ to ⟦_⟧₁ )
  open Environment        using ( ⟦_⟧ ; ≐→Equal )

  interp-prod : (p : Term {𝑆 = 𝑆} X)
    → ∀ ρ → ⟦ p ⟧₁ ⟨$⟩ ρ ≈ λ i → (⟦ 𝒜 i ⟧ p) ⟨$⟩ λ x → (ρ x) i
  interp-prod (ℊ x) = λ ρ i → ≐→Equal (𝒜 i) (ℊ x) (ℊ x) ≐-isRefl λ x' → (ρ x) i
  interp-prod (node f t) = λ ρ i → cong Interp (≡.refl , (λ j k → interp-prod (t j) ρ k)) i
```

#### Compatibility of terms

We now prove two important facts about term operations.  The first of these, which is
used very often in the sequel, asserts that every term commutes with every
homomorphism.

```agda
module _ {𝑆 : Signature 𝓞 𝓥}{𝑨 : Algebra {𝑆 = 𝑆} α ρᵃ}{𝑩 : Algebra {𝑆 = 𝑆} β ρᵇ}(hh : hom 𝑨 𝑩) where
  open Algebra 𝑨      using () renaming (Domain to A )
  open Setoid A       using () renaming ( Carrier to ∣A∣ )
  open Algebra 𝑩      using () renaming (Domain to B ; Interp to Interp₂ )
  open Setoid B       using ( _≈_ ; refl )
  open Environment 𝑨  using () renaming ( ⟦_⟧ to ⟦_⟧₁ )
  open Environment 𝑩  using () renaming ( ⟦_⟧ to ⟦_⟧₂ )
  open SetoidReasoning B
  open IsHom

  private
    h : A ⟶ B
    h = proj₁ hh

  comm-hom-term :
    (t : Term {𝑆 = 𝑆} X) (a : X → ∣A∣) → h ⟨$⟩ (⟦ t ⟧₁ ⟨$⟩ a) ≈ ⟦ t ⟧₂ ⟨$⟩ λ i → h ⟨$⟩ a i

  comm-hom-term (ℊ x) a = refl
  comm-hom-term (node f t) a = goal
    where
    goal : h ⟨$⟩ (⟦ node f t ⟧₁ ⟨$⟩ a) ≈ ⟦ node f t ⟧₂ ⟨$⟩ λ i → h ⟨$⟩ a i
    goal = begin
      h ⟨$⟩ (⟦ node f t ⟧₁ ⟨$⟩ a)                  ≈⟨ compatible (proj₂ hh) ⟩
      (f ^ 𝑩)(λ i → h ⟨$⟩ (⟦ t i ⟧₁ ⟨$⟩ a))        ≈⟨ cong Interp₂ (≡.refl , λ i → comm-hom-term (t i) a) ⟩
      (f ^ 𝑩)(λ i → ⟦ t i ⟧₂ ⟨$⟩ λ j → h ⟨$⟩ a j)  ≈⟨ refl ⟩
      ⟦ node f t ⟧₂ ⟨$⟩ (λ j → h ⟨$⟩ a j)          ∎
```

#### Substitution

A substitution from `Y` to `X` is simply a function from `Y` to `X`, and the
application of a substitution is represented as follows.

```agda
_[_]s : {χ : Level}{X Y : Type χ} → Term {𝑆 = 𝑆} Y → (Y → X) → Term {𝑆 = 𝑆} X
(ℊ y) [ σ ]s = ℊ (σ y)
(node f t)  [ σ ]s = node f λ i → t i [ σ ]s
```

Alternatively, we may want a substitution that replaces each variable symbol in `Y`,
not with an element of `X`, but with a term from `Term X`.

```agda
-- Substerm X Y, an inhabitant of which replaces each variable symbol in Y with a term from Term X.
Substerm : {𝑆 : Signature 𝓞 𝓥}(X Y : Type χ) → Type (ov {𝑆 = 𝑆} χ)
Substerm {𝑆 = 𝑆} X Y = (y : Y) → Term {𝑆 = 𝑆} X

-- Application of a Substerm.
_[_]t : {X Y : Type χ } → Term {𝑆 = 𝑆} Y → Substerm {𝑆 = 𝑆} X Y → Term {𝑆 = 𝑆} X
(ℊ y) [ σ ]t = σ y
(node f t) [ σ ]t = node f λ z → (t z) [ σ ]t
```
