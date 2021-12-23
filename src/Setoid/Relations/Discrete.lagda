---
layout: default
title : "Setoid.Relations.Discrete module (The Agda Universal Algebra Library)"
date : "2021-09-16"
author: "the agda-algebras development team"
---

### <a id="discrete-relations">Discrete Relations on Setoids</a>

This is the [Setoid.Relations.Discrete][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Setoid.Relations.Discrete where

-- Imports from Agda and the Agda Standard Library ----------------------------------------------
open import Agda.Primitive        using ( _⊔_ ; lsuc ) renaming ( Set to Type )
open import Data.Product          using ( _,_ ; _×_ )
open import Function.Bundles      using () renaming ( Func to _⟶_ )
open import Function.Base         using ( _∘_ )
open import Level                 using ( Level ; Lift )
open import Relation.Binary       using ( IsEquivalence ; Setoid )
open import Relation.Binary.Core  using ( _⇒_ ; _=[_]⇒_ ) renaming ( REL to BinREL ; Rel to BinRel )
open import Relation.Binary.Definitions
                                  using ( Reflexive ; Transitive )
open import Relation.Unary        using ( _∈_; Pred )
open import Relation.Binary.PropositionalEquality
                                  using ( _≡_ )

-- Imports from agda-algebras -------------------------------------------------------------------
open import Base.Overture.Preliminaries using ( Π-syntax )

private variable α β ρᵃ ρᵇ ℓ 𝓥 : Level
\end{code}

Here is a function that is useful for defining poitwise equality of functions wrt a given equality.

\begin{code}

open _⟶_ renaming ( f to _⟨$⟩_ )
module _ {𝐴 : Setoid α ρᵃ}{𝐵 : Setoid β ρᵇ} where
 open Setoid 𝐴 using () renaming ( Carrier to A ; _≈_ to _≈₁_ )
 open Setoid 𝐵 using () renaming ( Carrier to B ; _≈_ to _≈₂_ )

 function-equality : BinRel (𝐴 ⟶ 𝐵) (α ⊔ ρᵇ)
 function-equality f g = ∀ x → f ⟨$⟩ x ≈₂ g ⟨$⟩ x

\end{code}

Here is useful notation for asserting that the image of a function (the first argument)
is contained in a predicate, the second argument (a "subset" of the codomain).

\begin{code}

 Im_⊆_ : (𝐴 ⟶ 𝐵) → Pred B ℓ → Type (α ⊔ ℓ)
 Im f ⊆ S = ∀ x → f ⟨$⟩ x ∈ S

\end{code}


#### <a id="kernels">Kernels on setoids</a>

Given setoids 𝐴 and 𝐵 (with carriers A and B, resp), the *kernel* of a function `f : 𝐴 ⟶ 𝐵` is defined
informally by `{(x , y) ∈ A × A : f ⟨$⟩ x ≈₂ f ⟨$⟩ y}`.

\begin{code}

 fker : (𝐴 ⟶ 𝐵) → BinRel A ρᵇ
 fker g x y = g ⟨$⟩ x ≈₂ g ⟨$⟩ y

 fkerPred : (𝐴 ⟶ 𝐵) → Pred (A × A) ρᵇ
 fkerPred g (x , y) = g ⟨$⟩ x ≈₂ g ⟨$⟩ y

 open IsEquivalence

 fkerlift : (𝐴 ⟶ 𝐵) → (ℓ : Level) → BinRel A (ℓ ⊔ ρᵇ)
 fkerlift g ℓ x y = Lift ℓ (g ⟨$⟩ x ≈₂ g ⟨$⟩ y)

 -- The *identity relation* (equivalently, the kernel of a 1-to-1 function)
 0rel : {ℓ : Level} → BinRel A (ρᵃ ⊔ ℓ)
 0rel {ℓ} = λ x y → Lift ℓ (x ≈₁ y)


\end{code}

--------------------------------------

<span style="float:left;">[↑ Setoid.Relations](Setoid.Relations.html)</span>
<span style="float:right;">[Setoid.Relations.Quotients →](Setoid.Relations.Quotients.html)</span>

{% include UALib.Links.md %}
