---
layout: default
title : "Setoid.Varieties.EquationalLogic module (The Agda Universal Algebra Library)"
date : "2021-09-24"
author: "agda-algebras development team"
---

### Equational Logic and varieties of setoid algebras

This is the [Setoid.Varieties.EquationalLogic][] module of the [Agda Universal Algebra Library][] where the binary "models" relation ⊧, relating algebras (or classes of algebras) to the identities that they satisfy, is defined.

Let 𝑆 be a signature. By an *identity* or *equation* in 𝑆 we mean an ordered pair of terms, written 𝑝 ≈ 𝑞, from the term algebra 𝑻 X. If 𝑨 is an 𝑆-algebra we say that 𝑨 *satisfies* 𝑝 ≈ 𝑞 provided 𝑝 ̇ 𝑨 ≡ 𝑞 ̇ 𝑨 holds. In this situation, we write 𝑨 ⊧ 𝑝 ≈ 𝑞 and say that 𝑨 *models* the identity 𝑝 ≈ q. If 𝒦 is a class of algebras, all of the same signature, we write 𝒦 ⊧ p ≈ q if, for every 𝑨 ∈ 𝒦, 𝑨 ⊧ 𝑝 ≈ 𝑞.

Because a class of structures has a different type than a single structure, we must use a slightly different syntax to avoid overloading the relations ⊧ and ≈. As a reasonable alternative to what we would normally express informally as 𝒦 ⊧ 𝑝 ≈ 𝑞, we have settled on 𝒦 ⊫ p ≈ q to denote this relation.  To reiterate, if 𝒦 is a class of 𝑆-algebras, we write 𝒦 ⊫ 𝑝 ≈ 𝑞 if every 𝑨 ∈ 𝒦 satisfies 𝑨 ⊧ 𝑝 ≈ 𝑞.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature ; 𝑆)

module Setoid.Varieties.EquationalLogic where

-- Imports from Agda and the Agda Standard Library -------------------------------
open import Agda.Primitive   using () renaming ( Set to Type )
open import Data.Product     using ( _×_ ; _,_ ; Σ-syntax ; proj₁ ; proj₂ )
open import Function         using () renaming ( Func to _⟶_ )
open import Level            using ( _⊔_ ; Level )
open import Relation.Binary  using ( Setoid )
open import Relation.Unary   using ( Pred ; _∈_ )

-- Imports from the Agda Universal Algebra Library -------------------------------
open import Setoid.Algebras using ( Algebra ; ov )
open import Overture.Terms using ( Term )
open import Setoid.Terms using ( module Environment )

private variable χ α ρᵃ ℓ ι : Level
```
-->


#### The models relation

We define the binary "models" relation `⊧` using infix syntax so that we may
write, e.g., `𝑨 ⊧ p ≈ q` or `𝒦 ⊫ p ≈ q`, relating algebras (or classes of
algebras) to the identities that they satisfy. We also prove a couple of useful
facts about ⊧.  More will be proved about ⊧ in the next module,
Varieties.EquationalLogic.

```agda
open _⟶_ using () renaming ( to to _⟨$⟩_ )

module _  {X : Type χ} where

  open Setoid   using ( Carrier )
  open Algebra  using ( Domain )

  _⊧_≈_ : Algebra {𝑆 = 𝑆} α ρᵃ → Term {𝑆 = 𝑆} X → Term {𝑆 = 𝑆} X → Type _
  𝑨 ⊧ p ≈ q = ∀ (ρ : Carrier (Env X)) → ⟦ p ⟧ ⟨$⟩ ρ ≈ ⟦ q ⟧ ⟨$⟩ ρ
    where
    open Setoid ( Domain 𝑨 )  using ( _≈_ )
    open Environment 𝑨        using ( Env ; ⟦_⟧ )
  infix 10 _⊧_≈_

  _⊫_≈_ : Pred(Algebra {𝑆 = 𝑆} α ρᵃ) ℓ → Term {𝑆 = 𝑆} X → Term {𝑆 = 𝑆} X → Type (χ ⊔ ℓ ⊔ ov(α ⊔ ρᵃ))
  𝒦 ⊫ p ≈ q = {𝑨 : Algebra {𝑆 = 𝑆} _ _} → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q
```

(**Unicode tip**. Type \models to get `⊧` ; type \||= to get `⊫`.)

The expression `𝑨 ⊧ p ≈ q` represents the assertion that the identity `p ≈ q`
holds when interpreted in the algebra `𝑨` for any environment ρ; syntactically, we write
this interpretation as `⟦ p ⟧ ρ ≈ ⟦ q ⟧ ρ`. (Recall, and environment is simply an
assignment of values in the domain to variable symbols).


#### Equational theories and models over setoids

If 𝒦 denotes a class of structures, then `Th 𝒦` represents the set of identities
modeled by the members of 𝒦.

```agda
  Th' : Pred (Algebra {𝑆 = 𝑆} α ρᵃ) ℓ → Pred(Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X) (χ ⊔ ℓ ⊔ ov(α ⊔ ρᵃ))
  Th' 𝒦 = λ (p , q) → 𝒦 ⊫ p ≈ q

Th'' :  {χ α : Level}{X : Type χ} → Pred (Algebra {𝑆 = 𝑆} α α) (ov {𝑆 = 𝑆} α)
  →      Pred(Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X) (χ ⊔ ov {𝑆 = 𝑆} α)
Th'' 𝒦 = λ (p , q) → 𝒦 ⊫ p ≈ q
```

Perhaps we want to represent Th 𝒦 as an indexed collection.  We do so
essentially by taking `Th 𝒦` itself to be the index set, as shown below.

```agda
module _ {X : Type χ}{𝒦 : Pred (Algebra {𝑆 = 𝑆} α ρᵃ) (ov {𝑆 = 𝑆} α)} where
  ℐ : Type (ov(α ⊔ ρᵃ ⊔ χ))
  ℐ = Σ[ (p , q) ∈ (Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X) ] 𝒦 ⊫ p ≈ q

  ℰ : ℐ → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X
  ℰ ((p , q) , _) = (p , q)
```

If `ℰ` denotes a set of identities, then `Mod ℰ` is the class of structures
satisfying the identities in `ℰ`.

```agda
  Mod' : Pred(Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X) (ov {𝑆 = 𝑆} α) → Pred(Algebra {𝑆 = 𝑆} α ρᵃ) (ρᵃ ⊔ ov(α ⊔ χ))
  Mod' ℰ = λ 𝑨 → ∀ p q → (p , q) ∈ ℰ → 𝑨 ⊧ p ≈ q
```

It is sometimes more convenient to have a "tupled" version of the previous definition, which we denote by `Modᵗ` and define as follows.

```agda
  Modᵗ : {I : Type ι} → (I → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X) → {α : Level} → Pred(Algebra {𝑆 = 𝑆} α ρᵃ) (χ ⊔ ρᵃ ⊔ ι ⊔ α)
  Modᵗ ℰ = λ 𝑨 → ∀ i → 𝑨 ⊧ proj₁ (ℰ i) ≈ proj₂ (ℰ i)
```
