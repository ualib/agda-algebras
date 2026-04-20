---
layout: default
title : "Demos.HSP module"
date : "2022-04-27"
author: "the agda-algebras development team"
---

### <a id="inconsistency-in-first-formalization-attempt">Inconsistency in first formalization attempt</a>

\begin{code}
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Demos.ContraX {𝑆 : Signature 𝓞 𝓥} where
open import  Data.Unit.Polymorphic                  using ( ⊤ ; tt )
open import  Data.Empty.Polymorphic                 using ( ⊥ )
open import  Level                                  using ( 0ℓ )
open import  Relation.Binary                        using ( Setoid )
open import  Relation.Binary.PropositionalEquality  using ( setoid )
open import  Data.Product                           using ( Σ-syntax )
open import  Function    renaming (Func to _⟶_ )    using ()


open import Overture                 using ( ∣_∣ ; ∥_∥ )
open import Setoid.Algebras {𝑆 = 𝑆}  using ( Algebra ; 𝔻[_] )
open import Setoid.Functions         using (IsSurjective ; Image_∋_)

open Algebra

_↠_ : Set → Algebra 0ℓ 0ℓ → _
X ↠ 𝑨 = Σ[ h ∈ (setoid X ⟶ 𝔻[ 𝑨 ])] IsSurjective h

myA : Setoid 0ℓ 0ℓ
myA = record  { Carrier = ⊤
              ; _≈_ = λ x x₁ → ⊤
              ; isEquivalence = record  { refl = tt
                                        ; sym = λ _ → tt
                                        ; trans = λ _ _ → tt } }

myAlg : Algebra _ _
myAlg = record { Domain = myA ; Interp = _ }

contradiction : (∀ X 𝑨 → X ↠ 𝑨) → ⊥
contradiction h1 = ex falso
 where
 h : Σ[ h ∈ (setoid ⊥ ⟶ 𝔻[ myAlg ])] IsSurjective h
 h = h1 ⊥ myAlg

 falso : Image ∣ h ∣ ∋ tt
 falso = ∥ h ∥

 ex : Image ∣ h ∣ ∋ tt → ⊥
 ex (Image_∋_.eq a x) = a
\end{code}
