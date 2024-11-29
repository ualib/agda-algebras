
{-# OPTIONS --without-K --exact-split --safe #-}

open import Overture using (𝓞 ; 𝓥 ; Signature)

module Setoid.Varieties.EquationalLogic {𝑆 : Signature 𝓞 𝓥} where

open import Agda.Primitive   using () renaming ( Set to Type )
open import Data.Product     using ( _×_ ; _,_ ; Σ-syntax)
                             renaming ( proj₁ to fst ; proj₂ to snd )
open import Function         using () renaming ( Func to _⟶_ )
open import Level            using ( _⊔_ ; Level )
open import Relation.Binary  using ( Setoid )
open import Relation.Unary   using ( Pred ; _∈_ )

open import Setoid.Algebras  {𝑆 = 𝑆} using ( Algebra ; ov )
open import Base.Terms       {𝑆 = 𝑆} using ( Term )
open import Setoid.Terms     {𝑆 = 𝑆} using ( 𝑻 ; module Environment )

private variable χ α ρᵃ ℓ ι : Level

open _⟶_ using () renaming ( to to _⟨$⟩_ )

module _  {X : Type χ} where

 open Setoid   using () renaming (Carrier to ∣_∣ )
 open Algebra  using ( Domain )

 _⊧_≈_ : Algebra α ρᵃ → Term X → Term X → Type _
 𝑨 ⊧ p ≈ q = ∀ (ρ : ∣ Env X ∣) → ⟦ p ⟧ ⟨$⟩ ρ ≈ ⟦ q ⟧ ⟨$⟩ ρ
  where
  open Setoid ( Domain 𝑨 )  using ( _≈_ )
  open Environment 𝑨        using ( Env ; ⟦_⟧ )

 _⊫_≈_ : Pred(Algebra α ρᵃ) ℓ → Term X → Term X → Type (χ ⊔ ℓ ⊔ ov(α ⊔ ρᵃ))
 𝒦 ⊫ p ≈ q = {𝑨 : Algebra _ _} → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q

 Th' : Pred (Algebra α ρᵃ) ℓ → Pred(Term X × Term X) (χ ⊔ ℓ ⊔ ov(α ⊔ ρᵃ))
 Th' 𝒦 = λ (p , q) → 𝒦 ⊫ p ≈ q

Th'' :  {χ α : Level}{X : Type χ} → Pred (Algebra α α) (ov α)
 →      Pred(Term X × Term X) (χ ⊔ ov α)
Th'' 𝒦 = λ (p , q) → 𝒦 ⊫ p ≈ q

module _ {X : Type χ}{𝒦 : Pred (Algebra α ρᵃ) (ov α)} where

 ℐ : Type (ov(α ⊔ ρᵃ ⊔ χ))
 ℐ = Σ[ (p , q) ∈ (Term X × Term X) ] 𝒦 ⊫ p ≈ q

 ℰ : ℐ → Term X × Term X
 ℰ ((p , q) , _) = (p , q)

 Mod' : Pred(Term X × Term X) (ov α) → Pred(Algebra α ρᵃ) (ρᵃ ⊔ ov(α ⊔ χ))
 Mod' ℰ = λ 𝑨 → ∀ p q → (p , q) ∈ ℰ → 𝑨 ⊧ p ≈ q

 Modᵗ : {I : Type ι} → (I → Term X × Term X) → {α : Level} → Pred(Algebra α ρᵃ) (χ ⊔ ρᵃ ⊔ ι ⊔ α)
 Modᵗ ℰ = λ 𝑨 → ∀ i → 𝑨 ⊧ fst (ℰ i) ≈ snd (ℰ i)

