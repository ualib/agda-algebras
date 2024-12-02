
{-# OPTIONS --without-K --exact-split --safe #-}

module Base.Categories.Functors where

open import Agda.Primitive                         using ( _⊔_ ; lsuc ; Level )
                                                   renaming ( Set to Type ; lzero to ℓ₀ )
open import Data.Nat                               using ( ℕ ; zero ; suc ; _>_ )
open import Data.Sum.Base                          using ( _⊎_ ) renaming ( inj₁ to inl ;  inj₂ to inr )
open import Data.Product                           using ( Σ-syntax ; _,_ ; _×_ )
open import Data.Unit                              using ( tt ) renaming ( ⊤ to ⊤₀ )
open import Data.Unit.Polymorphic                  using ( ⊤ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; _≢_ )
open import Level

private variable α β : Level

infixl 6 _⊕_
infixr 7 _⊗_

data Functor₀ : Type (lsuc ℓ₀) where
 Id : Functor₀
 Const : Type → Functor₀
 _⊕_ : Functor₀ → Functor₀ → Functor₀
 _⊗_ : Functor₀ → Functor₀ → Functor₀

[_]₀ : Functor₀ → Type → Type
[ Id ]₀ B = B
[ Const C ]₀ B = C
[ F ⊕ G ]₀ B = [ F ]₀ B ⊎ [ G ]₀ B
[ F ⊗ G ]₀ B = [ F ]₀ B × [ G ]₀ B

data Functor {ℓ : Level} : Type (lsuc ℓ) where
 Id : Functor
 Const : Type ℓ → Functor
 _⊕_ : Functor{ℓ} → Functor{ℓ} → Functor
 _⊗_ : Functor{ℓ} → Functor{ℓ} → Functor

[_]_ : Functor → Type α → Type α
[ Id ] B = B
[ Const C ] B = C
[ F ⊕ G ] B = [ F ] B ⊎ [ G ] B
[ F ⊗ G ] B = [ F ] B × [ G ] B

{- from Mimram's talk (MFPS 2021):
record Poly (I J : Type) : Type (lsuc ℓ₀) where
 field
  Op : J → Type
  Pm : (i : I) → {j : J} → Op j → Type
-}

data μ_ (F : Functor) : Type where
 inn : [ F ] (μ F) → μ F

data list (A : Type) : Type ℓ₀ where
 [] : list A
 _∷_ : A → list A → list A

L : {ℓ : Level}(A : Type ℓ) → Functor{ℓ}
L A = Const ⊤ ⊕ (Const A ⊗ Id)

List : (A : Type) → Type ℓ₀
List A = μ (L A)

data Option (A : Type) : Type where
 some : A → Option A
 none : Option A

_[_] : {A : Type} → List A → ℕ → Option A
inn (inl x) [ n ] = none
inn (inr (x , xs)) [ zero ] = some x
inn (inr (x , xs)) [ suc n ] = xs [ n ]

_⟦_⟧ : {A : Type} → list A → ℕ → Option A
[] ⟦ n ⟧ = none
(x ∷ l) ⟦ zero ⟧ = some x
(x ∷ l) ⟦ suc n ⟧ = l ⟦ n ⟧

