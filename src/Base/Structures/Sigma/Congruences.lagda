---
layout: default
title : "Base.Structures.Sigma.Congruences module"
date : "2021-05-12"
author: "agda-algebras development team"
---

#### <a id="congruences-of-general-structures">Congruences of general structures</a>

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Base.Structures.Sigma.Congruences where

-- Imports from the Agda Standard Library ------------------------------------------------
open import Agda.Primitive  using ( _⊔_ ; lsuc ) renaming ( Set to Type ; lzero to ℓ₀ )
open import Data.Product    using ( _,_ ; _×_ ; Σ-syntax ) renaming ( proj₁ to fst )
open import Function.Base   using ( _∘_ )
open import Level           using ( Level ; Lift ; lift ; lower )
open import Relation.Unary  using ( Pred ; _∈_ )
open import Relation.Binary using ( IsEquivalence ) renaming ( Rel to BinRel )
open import Relation.Binary.PropositionalEquality using ( _≡_ )

-- Imports from the Agda Universal Algebra Library ---------------------------------------
open import Base.Overture.Preliminaries  using ( ∣_∣ )
open import Base.Equality.Welldefined    using ( swelldef )
open import Base.Relations.Discrete      using ( _|:_ ; 0[_] )
open import Base.Relations.Quotients     using ( Equivalence ; ⟪_⟫ ; ⌞_⌟ ; 0[_]Equivalence )
                                         using ( _/_ ; ⟪_∼_⟫-elim ; Quotient )
open import Base.Structures.Sigma.Basic  using ( Signature ; Structure ; _ᵒ_ ; Compatible ; _ʳ_ )

private variable 𝑅 𝐹 : Signature

module _ {α ρ : Level} where

 Con : (𝑨 : Structure 𝑅 𝐹 {α}{ρ}) → Type (lsuc (α ⊔ ρ))
 Con 𝑨 = Σ[ θ ∈ Equivalence ∣ 𝑨 ∣{α ⊔ ρ} ] (Compatible 𝑨 ∣ θ ∣)

 -- The zero congruence of a structure.
 0[_]Compatible : (𝑨 : Structure 𝑅 𝐹 {α}{ρ}) → swelldef ℓ₀ α
  →               (𝑓 : ∣ 𝐹 ∣) → (𝑓 ᵒ 𝑨) |: (0[ ∣ 𝑨 ∣ ]{ρ})

 0[ 𝑨 ]Compatible wd 𝑓 {i}{j} ptws0  = lift γ
  where
  γ : (𝑓 ᵒ 𝑨) i ≡ (𝑓 ᵒ 𝑨) j
  γ = wd (𝑓 ᵒ 𝑨) i j (lower ∘ ptws0)

 0Con[_] : (𝑨 : Structure 𝑅 𝐹 {α}{ρ}) → swelldef ℓ₀ α → Con 𝑨
 0Con[ 𝑨 ] wd = 0[ ∣ 𝑨 ∣ ]Equivalence , 0[ 𝑨 ]Compatible wd

\end{code}


#### <a id="quotient-structures">Quotients of structures of sigma type</a>

\begin{code}

 _╱_ : (𝑨 : Structure 𝑅 𝐹 {α}{ρ}) → Con 𝑨 → Structure 𝑅 𝐹 {lsuc (α ⊔ ρ)}{ρ}

 𝑨 ╱ θ = (Quotient (∣ 𝑨 ∣) {α ⊔ ρ} ∣ θ ∣)        -- domain of quotient structure
          , (λ r x → (r ʳ 𝑨) λ i → ⌞ x i ⌟)      -- interpretation of relations
          , λ f b → ⟪ (f ᵒ 𝑨) (λ i → ⌞ b i ⌟)  ⟫ -- interp of operations

 /≡-elim : {𝑨 : Structure 𝑅 𝐹 {α}{ρ}}( (θ , _ ) : Con 𝑨){u v : ∣ 𝑨 ∣}
  →    ⟪ u ⟫{∣ θ ∣} ≡ ⟪ v ⟫ → ∣ θ ∣ u v
 /≡-elim θ {u}{v} x =  ⟪ u ∼ v ⟫-elim {R = ∣ θ ∣} x

\end{code}

#### <a id="the-zero-congruence-of-an-arbitrary-structure">The zero congruence of an arbitrary structure</a>

\begin{code}

 𝟘[_╱_] : (𝑨 : Structure 𝑅 𝐹 {α}{ρ})(θ : Con 𝑨) → BinRel (∣ 𝑨 ∣ / (fst ∣ θ ∣)) (lsuc (α ⊔ ρ))
 𝟘[ 𝑨 ╱ θ ] = λ u v → u ≡ v

𝟎[_╱_] : {α ρ : Level}(𝑨 : Structure 𝑅 𝐹 {α}{ρ})(θ : Con 𝑨) → swelldef ℓ₀ (lsuc (α ⊔ ρ)) → Con (𝑨 ╱ θ)
𝟎[ 𝑨 ╱ θ ] wd = 0[ ∣ 𝑨 ╱ θ ∣ ]Equivalence , 0[ 𝑨 ╱ θ ]Compatible wd

\end{code}

--------------------------------

<span style="float:left;">[← Base.Structures.Sigma.Products](Base.Structures.Sigma.Products.html)</span>
<span style="float:right;">[Base.Structures.Sigma.Homs →](Base.Structures.Sigma.Homs.html)</span>

{% include UALib.Links.md %}
