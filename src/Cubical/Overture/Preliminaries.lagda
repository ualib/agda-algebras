---
layout: default
title : Cubical.Overture.Preliminaries module (of the agda-algebras library)
date : 2021-05-08
author: William DeMeo
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --cubical #-}

-- Imports from the Agda (Builtin) and the Agda Standard Library
open import Agda.Primitive using (_⊔_; lsuc)

-- Imports from Cubical Agda
open import Cubical.Core.Primitives using (_≡_; Type; Level; Σ-syntax; fst; snd; _,_)
open import Cubical.Foundations.Prelude using (refl; sym; _∙_; Lift; lift; lower)
open import Cubical.Foundations.Function using (_∘_)

module Cubical.Overture.Preliminaries where

variable
 α β : Level

{-Pi types. The dependent function type is traditionally denoted with a Pi symbol
  typically arranged as Π(x : A) B x, or something similar.  In Agda syntax, one writes
  `(x : A) → B x` for the dependent function type, but may use syntax that is closer
  to the standard Π notation and made available in Agda as follows.-}
Π : {A : Type α } (B : A → Type β ) → Type (α ⊔ β)   -- `\lub` ↝ ⊔
Π {A = A} B = (x : A) → B x
Π-syntax : (A : Type α)(B : A → Type β) → Type (α ⊔ β)
Π-syntax A B = Π B
syntax Π-syntax A (λ x → B) = Π[ x ∈ A ] B
infix 6 Π-syntax


module _ {A : Type α }{B : A → Type β} where

 ∣_∣ : Σ[ x ∈ A ] B x → A
 ∣ x , y ∣ = x

 ∥_∥ : (z : Σ[ a ∈ A ] B a) → B ∣ z ∣
 ∥ x , y ∥ = y

 infix  40 ∣_∣ ∥_∥

_⁻¹ : {A : Type α} {x y : A} → x ≡ y → y ≡ x
p ⁻¹ = sym p
infix  40 _⁻¹

id : {A : Type α} → A → A
id x = x

𝑖𝑑 : (A : Type α ) → A → A
𝑖𝑑 A = λ x → x

lift∼lower : {A : Type α} → lift ∘ lower ≡ 𝑖𝑑 (Lift {j = β} A)
lift∼lower = refl

lower∼lift : {A : Type α} → lower {α}{β}(lift {α}{β}(λ x → x)) ≡ 𝑖𝑑 A
lower∼lift = refl

_≈_ : {A : Type α } {B : A → Type β } → Π B → Π B → Type (α ⊔ β)
f ≈ g = ∀ x → f x ≡ g x

infix 8 _≈_

\end{code}

-------------------------------------------------------------------
--                        THE END                                --
-------------------------------------------------------------------









