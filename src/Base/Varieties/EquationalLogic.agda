
{-# OPTIONS --without-K --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Base.Varieties.EquationalLogic {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive  using () renaming ( Set to Type )
open import Data.Product    using ( _×_ ; _,_ ; Σ-syntax)
                            renaming ( proj₁ to fst ; proj₂ to snd )
open import Level           using ( Level ;  _⊔_ )
open import Relation.Unary  using ( Pred ; _∈_ )

open import Overture                using ( _≈_ )
open import Base.Algebras  {𝑆 = 𝑆}  using ( Algebra ; ov )
open import Base.Terms     {𝑆 = 𝑆}  using ( Term ; 𝑻 ; _⟦_⟧ )

private variable
 χ α ρ ι : Level
 X : Type χ

_⊧_≈_ : Algebra α → Term X → Term X → Type _
𝑨 ⊧ p ≈ q = 𝑨 ⟦ p ⟧ ≈ 𝑨 ⟦ q ⟧

_⊫_≈_ : Pred(Algebra α) ρ → Term X → Term X → Type _
𝒦 ⊫ p ≈ q = {𝑨 : Algebra _} → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q

Th : Pred (Algebra α) (ov α) → Pred(Term X × Term X) _
Th 𝒦 = λ (p , q) → 𝒦 ⊫ p ≈ q

module _ {X : Type χ}{𝒦 : Pred (Algebra α) (ov α)} where

 ℐ : Type (ov(α ⊔ χ))
 ℐ = Σ[ (p , q) ∈ (Term X × Term X) ] 𝒦 ⊫ p ≈ q

 ℰ : ℐ → Term X × Term X
 ℰ ((p , q) , _) = (p , q)

Mod : Pred(Term X × Term X) (ov α) → Pred(Algebra α) _
Mod ℰ = λ 𝑨 → ∀ p q → (p , q) ∈ ℰ → 𝑨 ⊧ p ≈ q
Modᵗ : {I : Type ι} → (I → Term X × Term X) → {α : Level} → Pred(Algebra α) _
Modᵗ ℰ = λ 𝑨 → ∀ i → 𝑨 ⊧ (fst (ℰ i)) ≈ (snd (ℰ i))

