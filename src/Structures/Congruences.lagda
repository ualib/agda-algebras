---
layout: default
title : Structures.Congruences.Records module
date : 2021-05-28
author: [agda-algebras development team][]
---


#### Congruences for structures as records

This module is similar to Congruences.lagda but for structures represented using records rather than
dependent pair type.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Structures.Congruences where

-- imports from Agda and the Agda Standard Library -------------------------------------------
open import Agda.Primitive using ( _⊔_ ; lsuc ) renaming ( Set  to Type )
open import Data.Product   using ( _,_ ; _×_ ; Σ-syntax ) renaming ( proj₁ to fst )
open import Function.Base  using ( _∘_ )
open import Level          using ( Level ; Lift ; lift ; lower )
open import Relation.Binary.PropositionalEquality
                           using ( _≡_ ; refl )


-- imports from agda-algebras --------------------------------------------------------------
open import Overture.Preliminaries using ( ∣_∣ )
open import Relations.Discrete     using ( _|:_ ; 0[_] )
open import Relations.Quotients    using ( Equivalence ; Quotient ; 0[_]Equivalence
                                         ; ⟪_⟫ ; ⌞_⌟ ; ⟪_∼_⟫-elim ; _/_ )
open import Foundations.Welldefined using ( swelldef )
open import Structures.Basic        using ( signature ; structure ; sigl ; siglʳ
                                          ; compatible )

private variable
 𝓞₀ 𝓥₀ 𝓞₁ 𝓥₁ : Level
 𝐹 : signature 𝓞₀ 𝓥₀
 𝑅 : signature 𝓞₁ 𝓥₁
 α ρ : Level

open signature
open structure

con : ∀ {α ρ} → structure 𝐹 𝑅 {α}{ρ} → Type (sigl 𝐹 ⊔ lsuc α ⊔ lsuc ρ)
con {α = α}{ρ} 𝑨 = Σ[ θ ∈ Equivalence (carrier 𝑨){α ⊔ ρ} ] (compatible 𝑨 ∣ θ ∣)


-- Example. The zero congruence of a structure.
0[_]compatible : (𝑨 : structure 𝐹 𝑅 {α} {ρ}) → swelldef (siglʳ 𝐹) α
 →               (𝑓 : symbol 𝐹) → (op 𝑨) 𝑓 |: (0[ carrier 𝑨 ] {ρ})

0[ 𝑨 ]compatible wd 𝑓 {i}{j} ptws0  = lift γ
 where
 γ : ((op 𝑨) 𝑓) i ≡ ((op 𝑨) 𝑓) j
 γ = wd ((op 𝑨) 𝑓) i j (lower ∘ ptws0)

0con[_] : (𝑨 : structure 𝐹 𝑅 {α} {ρ}) → swelldef (siglʳ 𝐹) α → con 𝑨
0con[ 𝑨 ] wd = 0[ carrier 𝑨 ]Equivalence , 0[ 𝑨 ]compatible wd

-- Quotient structures

_╱_  -- alias  (useful on when signature and universe parameters can be inferred)
 quotient : (𝑨 : structure 𝐹 𝑅 {α}{ρ}) → con 𝑨 → structure 𝐹 𝑅
quotient 𝑨 θ = record
            { carrier = Quotient (carrier 𝑨) ∣ θ ∣     -- domain of quotient structure
            ; op = λ f b → ⟪ ((op 𝑨) f) (λ i → ⌞ b i ⌟) ⟫ {fst ∣ θ ∣} -- interp of operations
            ; rel = λ r x → ((rel 𝑨) r) (λ i → ⌞ x i ⌟)   -- interpretation of relations
            }

_╱_ = quotient


/≡-elim : {𝑨 : structure 𝐹 𝑅 {α}{ρ}} ((θ , _ ) : con 𝑨){u v : carrier 𝑨}
 →        ⟪ u ⟫ {∣ θ ∣} ≡ ⟪ v ⟫ {∣ θ ∣} → ∣ θ ∣ u v
/≡-elim θ {u}{v} x =  ⟪ u ∼ v ⟫-elim{R = ∣ θ ∣} x



-- Example. The zero congruence of a quotient structure.
𝟎[_╱_] : (𝑨 : structure 𝐹 𝑅 {α}{ρ}) (θ : con 𝑨)
 →       swelldef (siglʳ 𝐹)(lsuc (α ⊔ ρ)) → con (𝑨 ╱ θ)
𝟎[ 𝑨 ╱ θ ] wd = 0con[ 𝑨 ╱ θ ] wd

\end{code}


--------------------------------

<br>
<br>

[← Structures.Products](Structures.Products.html)
<span style="float:right;">[Structures.Homs →](Structures.Homs.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

