
{-# OPTIONS --without-K --exact-split --safe #-}

module Base.Relations.Properties where

open import Agda.Primitive        using () renaming ( Set to Type )
open import Data.Product          using ( _,_ ; _×_ )
open import Data.Sum.Base         using ( _⊎_ )
open import Level                 using ( Level )
open import Relation.Binary.Core  using ( ) renaming ( REL to BinREL ; Rel to BinRel )
open import Relation.Unary        using ( Pred ; _∈_ ; _∉_ )
open import Relation.Binary.PropositionalEquality
                                  using ( _≡_ )

private variable
 a b c α β γ ℓ : Level
 A : Set a
 B : Set b
 C : Set c

curry : Pred(A × B) ℓ → BinREL A B ℓ
curry P x y = (x , y) ∈ P

uncurry : BinREL A B ℓ → Pred(A × B) ℓ
uncurry _≈_ (a , b) = a ≈ b

Reflexive : Pred (A × A) ℓ → Type _
Reflexive P = ∀ {x} → (x , x) ∈ P

Sym : Pred (A × B) α → Pred (B × A) β → Type _
Sym P Q = ∀ {x y} → (x , y) ∈ P → (y , x) ∈ Q

Symmetric : Pred (A × A) ℓ → Type _
Symmetric P = Sym P P

Trans : Pred (A × B) α → Pred (B × C) β → Pred (A × C) γ → Type _
Trans P Q R = ∀ {i j k} → P (i , j) → Q (j , k) → R (i , k)

TransFlip : Pred (A × B) α → Pred (B × C) β → Pred(A × C) γ → Type _
TransFlip P Q R = ∀ {i j k} → Q (j , k) → P (i , j) → R (i , k)

Transitive : Pred (A × A) ℓ → Type _
Transitive P = Trans P P P

Antisym : Pred (A × B) α → Pred (B × A) β → Pred (A × B) γ → Type _
Antisym R S E = ∀ {i j} → R (i , j) → S (j , i) → E (i , j)

Antisymmetric : BinRel A α → Pred (A × A) β → Type _
Antisymmetric _≈_ P = Antisym P P (uncurry _≈_)

Irreflexive : BinREL A B α → Pred (A × B) β → Type _
Irreflexive _≈_ P = ∀ {x y} → x ≈ y → (x , y) ∉ P

Asymmetric : Pred (A × A) ℓ → Type _
Asymmetric P = ∀ {x y} → (x , y) ∈ P → (y , x) ∉ P

Connex : Pred (A × B) α → Pred (B × A) β → Type _
Connex P Q = ∀ x y → (x , y) ∈ P ⊎ (y , x) ∈ Q

Total : Pred (A × A) ℓ → Type _
Total P = Connex P P

