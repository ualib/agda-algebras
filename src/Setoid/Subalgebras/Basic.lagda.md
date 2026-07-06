---
layout: default
title : "Setoid.Subalgebras.Basic module (The Agda Universal Algebra Library)"
date : "2021-07-17"
author: "agda-algebras development team"
---

#### Subalgebras of setoid algebras

This is the [Setoid.Subalgebras.Basic][] module of the [Agda Universal Algebra Library][].


<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Subalgebras.Basic {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive using () renaming ( Set to Type )

-- imports from the Agda Standard Library ---------------------------------------------------
open import Data.Product                   using ( _,_ ; Σ-syntax ) renaming ( _×_ to _∧_ )
open import Level                          using ( Level ; _⊔_ )
open import Relation.Binary                using ( REL )
open import Relation.Unary                 using ( Pred ; _∈_ )

-- Imports from the Agda Universal Algebra Library ------------------------------------------
open import Overture                       using ( proj₁ ; proj₂ )
open import Setoid.Functions               using ( IsInjective )

open import Setoid.Algebras       {𝑆 = 𝑆}  using ( Algebra ; ov )
open import Setoid.Homomorphisms {𝑆 = 𝑆}
  using ( hom ; mon ; mon→intohom ; kerquo ; FirstHomTheorem )

private variable α ρᵃ β ρᵇ ℓ : Level
```
-->

```agda
_≥_   -- alias for supalgebra (aka overalgebra)
  _IsSupalgebraOf_ : Algebra α ρᵃ → Algebra β ρᵇ → Type _
𝑨 IsSupalgebraOf 𝑩 = Σ[ h ∈ hom 𝑩 𝑨 ] IsInjective (proj₁ h)

_≤_   -- alias for subalgebra relation
  _IsSubalgebraOf_ : Algebra α ρᵃ → Algebra β ρᵇ → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
𝑨 IsSubalgebraOf 𝑩 = Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective (proj₁ h)

-- Syntactic sugar for sup/sub-algebra relations.
𝑨 ≥ 𝑩 = 𝑨 IsSupalgebraOf 𝑩
𝑨 ≤ 𝑩 = 𝑨 IsSubalgebraOf 𝑩

mon→≤ : {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} → mon 𝑨 𝑩 → 𝑨 ≤ 𝑩
mon→≤ {𝑨 = 𝑨}{𝑩} x = mon→intohom 𝑨 𝑩 x

record SubalgebraOf : Type (ov (α ⊔ β ⊔ ρᵃ ⊔ ρᵇ)) where
  field
    algebra : Algebra α ρᵃ
    subalgebra : Algebra β ρᵇ
    issubalgebra : subalgebra ≤ algebra

Subalgebra : Algebra α ρᵃ → {β ρᵇ : Level} → Type _
Subalgebra 𝑨 {β}{ρᵇ} = Σ[ 𝑩 ∈ (Algebra β ρᵇ) ] 𝑩 ≤ 𝑨

{- usage note: for 𝑨 : Algebra α ρᵃ, an inhabitant of `Subalgebra 𝑨` is a pair
   `(𝑩 , p) : Subalgebra 𝑨`  providing
   - `𝑩 : Algebra β ρᵇ` and
   - `p : 𝑩 ≤ 𝑨`, a proof that 𝑩 is a subalgebra of 𝐴. -}

IsSubalgebraREL : {α ρᵃ β ρᵇ : Level} → REL (Algebra α ρᵃ)(Algebra β ρᵇ) ℓ → Type _
IsSubalgebraREL {α}{ρᵃ}{β}{ρᵇ} R = ∀ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} → 𝑨 ≤ 𝑩

record SubalgebraREL (R : REL (Algebra β ρᵇ)(Algebra α ρᵃ) ℓ) : Type (ov (α ⊔ β ⊔ ρᵇ ⊔ ℓ)) where
  field
    isSubalgebraREL : IsSubalgebraREL R
```

From now on we will use `𝑩 ≤ 𝑨` to express the assertion that `𝑩` is a subalgebra of `𝑨`.

#### Subalgebras of classes of setoid algebras

Suppose `𝒦 : Pred (Algebra α 𝑆) γ` denotes a class of `𝑆`-algebras and `𝑩 : Algebra β ρᵇ`
denotes an arbitrary `𝑆`-algebra.  Consider the assertion that `𝑩` is a subalgebra of
an algebra in the class `𝒦`.  With the next definition we can express this
assertion as `𝑩 IsSubalgebraOfClass 𝒦`.

```agda
_≤c_
  _IsSubalgebraOfClass_ : Algebra β ρᵇ → Pred (Algebra α ρᵃ) ℓ → Type _
𝑩 IsSubalgebraOfClass 𝒦 = Σ[ 𝑨 ∈ Algebra _ _ ] ((𝑨 ∈ 𝒦) ∧ (𝑩 ≤ 𝑨))

𝑩 ≤c 𝒦 = 𝑩 IsSubalgebraOfClass 𝒦  -- (alias)

record SubalgebraOfClass : Type (ov (α ⊔ β ⊔ ρᵃ ⊔ ρᵇ ⊔ ℓ)) where
  field
    class : Pred (Algebra α ρᵃ) ℓ
    subalgebra : Algebra β ρᵇ
    issubalgebraofclass : subalgebra ≤c class

record SubalgebraOfClass' : Type (ov (α ⊔ β ⊔ ρᵃ ⊔ ρᵇ ⊔ ℓ)) where
  field
    class : Pred (Algebra α ρᵃ) ℓ
    classalgebra : Algebra α ρᵃ
    isclassalgebra : classalgebra ∈ class
    subalgebra : Algebra β ρᵇ
    issubalgebra : subalgebra ≤ classalgebra

-- The collection of subalgebras of algebras in class 𝒦.
SubalgebrasOfClass : Pred (Algebra α ρᵃ) ℓ → {β ρᵇ : Level} → Type _
SubalgebrasOfClass 𝒦 {β}{ρᵇ} = Σ[ 𝑩 ∈ Algebra β ρᵇ ] 𝑩 ≤c 𝒦
```



#### Consequences of First Homomorphism Theorem

As an example use-case of the `IsSubalgebraOf` type defined above, we prove the
following easy but useful corollary of the First Homomorphism Theorem (proved
in the [Setoid.Homomorphisms.Noether][] module): If `𝑨` and `𝑩` are `𝑆`-algebras
and `h : hom 𝑨 𝑩` a homomorphism from `𝑨` to `𝑩`, then the quotient `𝑨 ╱ ker h`
is (isomorphic to) a subalgebra of `𝑩`.


```agda
FirstHomCorollary : {𝑨 : Algebra α ρᵃ} {𝑩 : Algebra β ρᵇ} (hh : hom 𝑨 𝑩)
  → (kerquo hh) IsSubalgebraOf 𝑩
FirstHomCorollary hh = proj₁ (FirstHomTheorem hh) , proj₂ (proj₂ (FirstHomTheorem hh))
```
