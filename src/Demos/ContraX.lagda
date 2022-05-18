\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

open import Base.Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Demos.ContraX {𝑆 : Signature 𝓞 𝓥} where
open import  Data.Unit.Polymorphic                  using ( ⊤ ; tt )
open import  Data.Empty.Polymorphic                 using ( ⊥ )
open import  Level                                  using ( 0ℓ )
open import  Relation.Binary                        using ( Setoid )
open import  Relation.Binary.PropositionalEquality  using ( setoid )
open import  Data.Product                           using ( Σ-syntax )
open import  Function    renaming (Func to _⟶_ )    using  ( )
open import Base.Overture.Preliminaries             using ( ∣_∣ ; ∥_∥ )
open import Setoid.Algebras.Basic           {𝑆 = 𝑆} using ( Algebra ; 𝔻[_] )
open import Setoid.Overture.Surjective              using (IsSurjective)
open import Setoid.Overture.Inverses                using (Image_∋_)

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
