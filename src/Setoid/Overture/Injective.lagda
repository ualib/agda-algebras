---
layout: default
title : "Setoid.Overture.Injective module"
date : "2021-09-13"
author: "the agda-algebras development team"
---

### <a id="injective-functions-on-setoids">Injective functions on setoids</a>

This is the [Setoid.Overture.Injective][] module of the [agda-algebras][] library.

We say that a function `f : A → B` from one setoid (A , ≈₀) to another (B , ≈₁) is *injective* (or *monic*) provided the following implications hold:  ∀ a₀ a₁ if f ⟨$⟩ a₀ ≈₁ f ⟨$⟩ a₁, then a₀ ≈₀ a₁.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Relation.Binary using ( Setoid )

module Setoid.Overture.Injective where


-- Imports from Agda and the Agda Standard Library -------------
open import Agda.Primitive        using ( _⊔_ ; Level )  renaming ( Set to Type )
open import Function.Bundles      using ( Injection )    renaming ( Func to _⟶_ )
open import Function.Base         using ( _∘_ ; id )
open import Relation.Binary.Core  using ( _Preserves_⟶_ )
open import Relation.Binary       using ( Rel )
import Function.Definitions as FD

-- Imports from agda-algebras -----------------------------------------------
open import Setoid.Overture.Preliminaries  using ( 𝑖𝑑 )  renaming ( _∘_ to _⟨∘⟩_ )
open import Setoid.Overture.Inverses       using ( Image_∋_ ; Inv )

private variable
 α β γ ρᵃ ρᵇ ρᶜ ℓ₁ ℓ₂ ℓ₃ : Level

\end{code}

A function `f : A ⟶ B` from one setoid `(A , ≈₀)` to another
`(B , ≈₁)` is called *injective* provided `∀ a₀ a₁`, if `f ⟨$⟩ a₀ ≈₁ f ⟨$⟩
a₁`, then `a₀ ≈₀ a₁`.  The [Agda Standard Library][] defines a type representing
injective functions on bare types and we use this type (called `Injective`) to
define our own type representing the property of being an injective function on
setoids (called `IsInjective`).

\begin{code}

module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where

 open Setoid 𝑨  using ()               renaming (Carrier to A; _≈_ to _≈₁_)
 open Setoid 𝑩  using ( trans ; sym )  renaming (Carrier to B; _≈_ to _≈₂_)

 open Injection {From = 𝑨}{To = 𝑩} using ( function ; injective )  renaming (f to _⟨$⟩_)
 open _⟶_ {a = α}{ρᵃ}{β}{ρᵇ}{From = 𝑨}{To = 𝑩}                    renaming (f to _⟨$⟩_ )
 open FD _≈₁_ _≈₂_

 IsInjective : (𝑨 ⟶ 𝑩) →  Type (α ⊔ ρᵃ ⊔ ρᵇ)
 IsInjective f = Injective (_⟨$⟩_ f)

 open Image_∋_

 -- Inverse of an injective function preserves setoid equalities
 LeftInvPreserves≈ : (F : Injection 𝑨 𝑩)
                     {b₀ b₁ : B}(u : Image (function F) ∋ b₀)(v : Image (function F) ∋ b₁)
  →                  b₀ ≈₂ b₁ → (Inv (function F) u) ≈₁ (Inv (function F) v)

 LeftInvPreserves≈ F {b₀}{b₁} (eq a₀ x₀) (eq a₁ x₁) bb = Goal
  where
  fa₀≈fa₁ : (F ⟨$⟩ a₀) ≈₂ (F ⟨$⟩ a₁)
  fa₀≈fa₁ = trans (sym x₀) (trans bb x₁)
  Goal : a₀ ≈₁ a₁
  Goal = injective F fa₀≈fa₁

\end{code}

Proving that the composition of injective functions is again injective
is simply a matter of composing the two assumed witnesses to injectivity.
(Note that here we are viewing the maps as functions on the underlying carriers
of the setoids; an alternative for setoid functions, called `∘-injective`, is proved below.)

\begin{code}

module compose {A : Type α}(_≈₁_ : Rel A ρᵃ)
               {B : Type β}(_≈₂_ : Rel B ρᵇ)
               {C : Type γ}(_≈₃_ : Rel C ρᶜ) where

 open FD {A = A} {B} _≈₁_ _≈₂_ using () renaming ( Injective to InjectiveAB )
 open FD {A = B} {C} _≈₂_ _≈₃_ using () renaming ( Injective to InjectiveBC )
 open FD {A = A} {C} _≈₁_ _≈₃_ using () renaming ( Injective to InjectiveAC )

 ∘-injective-bare : {f : A → B}{g : B → C} → InjectiveAB f → InjectiveBC g → InjectiveAC (g ∘ f)
 ∘-injective-bare finj ginj = finj ∘ ginj

\end{code}

The three lines that begin `open FD` illustrate one of the technical consequences
of the precision demanded in formal proofs. In the statements of the
`∘-injective-func` lemma, we must distinguish the (distinct) notions of injectivity, one
for each domain-codomain pair of setoids, and we do this with the `open FD`
lines which give each instance of injectivity a different name.

\begin{code}

module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} {𝑪 : Setoid γ ρᶜ} where
 open Setoid 𝑨   using () renaming ( Carrier to A ; _≈_ to _≈₁_ )
 open Setoid 𝑩   using () renaming ( Carrier to B )
 open Setoid 𝑪   using () renaming ( Carrier to C ; _≈_ to _≈₃_)
 open Injection  using () renaming ( function to fun )

 ∘-injective : (f : 𝑨 ⟶ 𝑩)(g : 𝑩 ⟶ 𝑪)
  →            IsInjective f → IsInjective g → IsInjective (g ⟨∘⟩ f)
 ∘-injective _ _ finj ginj = finj ∘ ginj

 ∘-injection : Injection 𝑨 𝑩 → Injection 𝑩 𝑪 → Injection 𝑨 𝑪
 ∘-injection fi gi = record { f = λ x → apg (apf x)
                            ; cong = conggf
                            ; injective = ∘-injective (fun fi) (fun gi) (injective fi) (injective gi)
                            }
  where
  open Injection
  apf : A → B
  apf = f fi
  apg : B → C
  apg = f gi
  conggf : (λ x → apg (apf x)) Preserves _≈₁_ ⟶ _≈₃_
  conggf {x}{y} x≈y = cong gi (cong fi x≈y)


id-is-injective : {𝑨 : Setoid α ρᵃ} → IsInjective{𝑨 = 𝑨}{𝑨} 𝑖𝑑
id-is-injective = id

\end{code}

--------------------------------------

<span style="float:left;">[← Setoid.Overture.Inverses](Setoid.Overture.Inverses.html)</span>
<span style="float:right;">[Setoid.Overture.Surjective →](Setoid.Overture.Surjective.html)</span>

{% include UALib.Links.md %}

