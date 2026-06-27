---
layout: default
title : "Setoid.Terms.Basic module (The Agda Universal Algebra Library)"
date : "2021-09-18"
author: "agda-algebras development team"
---

### Basic definitions

This is the [Setoid.Terms.Basic][] module of the [Agda Universal Algebra Library][].

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Terms.Basic {𝑆 : Signature 𝓞 𝓥} where

-- imports from Agda and the Agda Standard Library -------------------------------
open import Agda.Primitive         using () renaming ( Set to Type )
open import Data.Product           using ( _,_ )
open import Function               using ( Func )
open import Level                  using ( Level ; _⊔_ )
open import Relation.Binary        using ( Setoid ; IsEquivalence )
                                   using ( Reflexive ; Symmetric ; Transitive )

open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; trans )

-- Imports from the Agda Universal Algebra Library -------------------------------
open import Overture using ( ArityOf ; OperationSymbolsOf )
open import Setoid.Algebras  {𝑆 = 𝑆}  using ( Algebra ; ov ; _^_ ; 𝔻[_] ; 𝕌[_] )
open import Overture.Terms  {𝑆 = 𝑆} using ( Term )

open Func renaming ( to to _⟨$⟩_ )
open Term

private variable
 χ α ℓ : Level
 X Y : Type χ
```

#### Equality of terms

We take a different approach here, using Setoids instead of quotient types.
That is, we will define the collection of terms in a signature as a setoid
with a particular equality-of-terms relation, which we must define.
Ultimately we will use this to define the (absolutely free) term algebra
as a Algebra whose carrier is the setoid of terms.

```agda
module _ {X : Type χ } where

 -- Equality of terms as an inductive datatype
 data _≐_ : Term X → Term X → Type (ov χ) where
  rfl :  {x y : X} → x ≡ y → ℊ x ≐ ℊ y
  gnl :  {f : OperationSymbolsOf 𝑆}{s t : ArityOf 𝑆 f → Term X}
         → (∀ i → s i ≐ t i) → node f s ≐ node f t

 infix 4 _≐_

 -- Equality of terms is an equivalence relation
 ≐-isRefl : Reflexive _≐_
 ≐-isRefl {ℊ _} = rfl refl
 ≐-isRefl {node _ _} = gnl λ _ → ≐-isRefl

 ≐-isSym : Symmetric _≐_
 ≐-isSym (rfl x) = rfl (sym x)
 ≐-isSym (gnl x) = gnl λ i → ≐-isSym (x i)

 ≐-isTrans : Transitive _≐_
 ≐-isTrans (rfl x) (rfl y) = rfl (trans x y)
 ≐-isTrans (gnl x) (gnl y) = gnl λ i → ≐-isTrans (x i) (y i)

 ≐-isEquiv : IsEquivalence _≐_
 ≐-isEquiv = record { refl = ≐-isRefl ; sym = ≐-isSym ; trans = ≐-isTrans }

TermSetoid : (X : Type χ) → Setoid (ov χ) (ov χ)
TermSetoid X = record { Carrier = Term X ; _≈_ = _≐_ ; isEquivalence = ≐-isEquiv }

open Algebra

-- The Term Algebra
𝑻 : (X : Type χ) → Algebra (ov χ) (ov χ)
Domain (𝑻 X) = TermSetoid X
Interp (𝑻 X) ⟨$⟩ (f , ts) = node f ts
cong (Interp (𝑻 X)) (refl , ss≐ts) = gnl ss≐ts
```

#### Interpretation of terms in setoid algebras

The approach to terms and their interpretation in this module was inspired by
[Andreas Abel's formal proof of Birkhoff's completeness theorem](http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf).

A substitution from `Δ` to `Γ` associates a term in `Γ` with each variable in `Δ`.

```agda
-- Parallel substitutions.
Sub : Type χ → Type χ → Type (ov χ)
Sub X Y = (y : Y) → Term X

-- Application of a substitution.
_[_] : (t : Term Y) (σ : Sub X Y) → Term X
(ℊ x) [ σ ] = σ x
(node f ts) [ σ ] = node f (λ i → ts i [ σ ])

infix 30 _[_]
```

An environment for `Γ` maps each variable `x : Γ` to an element of `A`, and equality
of environments is defined pointwise.

```agda
module Environment (𝑨 : Algebra α ℓ) where
  open Algebra 𝑨 using() renaming(Interp  to InterpA )
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ )
    renaming  ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans)

  Env : Type χ → Setoid _ _
  Env X = record  { Carrier = X → 𝕌[ 𝑨 ]
                  ; _≈_ = λ ρ ρ' → (x : X) → ρ x ≈ ρ' x
                  ; isEquivalence = record  { refl = λ _ → ≈refl
                                            ; sym = λ h x → ≈sym (h x)
                                            ; trans = λ g h x → ≈trans (g x) (h x)
                                            }
                  }

  open Algebra using ( Domain ; Interp )

  EnvAlgebra : Type χ → Algebra (α ⊔ χ) (ℓ ⊔ χ)
  Domain (EnvAlgebra X) = Env X
  Interp (EnvAlgebra X) ⟨$⟩ (f , aϕ) = λ x → (f ^ 𝑨) λ i → aϕ i x
  cong (Interp (EnvAlgebra X)) {f , a} {.f , b} (refl , aibi) x = cong InterpA (refl , λ i → aibi i x)
```


Interpretation of terms is iteration on the W-type. The standard library offers `iter' (on sets), but we need this to be a setoid function.


```agda
  ⟦_⟧ : {X : Type χ}(t : Term X) → Func (Env X) 𝔻[ 𝑨 ]
  ⟦ ℊ x ⟧          ⟨$⟩ ρ = ρ x
  ⟦ node f args ⟧  ⟨$⟩ ρ = InterpA ⟨$⟩ (f , λ i → ⟦ args i ⟧ ⟨$⟩ ρ)
  cong ⟦ ℊ x ⟧          u≈v = u≈v x
  cong ⟦ node f args ⟧  x≈y = cong InterpA (refl , λ i → cong ⟦ args i ⟧ x≈y )

  open Setoid using ( Carrier )

  -- An equality between two terms holds in a model if the two terms
  -- are equal under all valuations of their free variables.
  Equal : ∀ {X : Type χ} (s t : Term X) → Type _
  Equal {X = X} s t = ∀ (ρ : Carrier (Env X)) → ⟦ s ⟧ ⟨$⟩ ρ ≈ ⟦ t ⟧ ⟨$⟩ ρ

  ≐→Equal : {X : Type χ}(s t : Term X) → s ≐ t → Equal s t
  ≐→Equal .(ℊ _) .(ℊ _) (rfl refl) = λ _ → ≈refl
  ≐→Equal (node _ s) (node _ t) (gnl x) =
    λ ρ → cong InterpA (refl , λ i → ≐→Equal (s i) (t i) (x i) ρ)

  -- Equal is an equivalence relation.
  isEquiv : {Γ : Type χ} → IsEquivalence (Equal {X = Γ})
  isEquiv .IsEquivalence.refl = λ _ → ≈refl
  isEquiv .IsEquivalence.sym = λ x=y ρ → ≈sym (x=y ρ)
  isEquiv .IsEquivalence.trans = λ ij jk ρ → ≈trans (ij ρ) (jk ρ)

  -- Evaluation of a substitution gives an environment.
  ⟦_⟧s : {X Y : Type χ} → Sub X Y → Carrier (Env X) → Carrier (Env Y)
  ⟦ σ ⟧s ρ x = ⟦ σ x ⟧ ⟨$⟩ ρ

  -- Substitution lemma: ⟦t[σ]⟧ρ ≃ ⟦t⟧⟦σ⟧ρ
  substitution :  {X Y : Type χ} → (t : Term Y) (σ : Sub X Y) (ρ : Carrier (Env X))
    → ⟦ t [ σ ] ⟧ ⟨$⟩ ρ  ≈  ⟦ t ⟧ ⟨$⟩ (⟦ σ ⟧s ρ)

  substitution (ℊ x) σ ρ = ≈refl
  substitution (node f ts) σ ρ = cong InterpA (refl , λ i → substitution (ts i) σ ρ)
```


--------------------------------

<span style="float:left;">[↑ Setoid.Terms](Setoid.Terms.html)</span>
<span style="float:right;">[Setoid.Terms.Properties →](Setoid.Terms.Properties.html)</span>

{% include UALib.Links.md %}
