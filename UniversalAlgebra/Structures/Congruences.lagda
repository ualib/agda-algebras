---
layout: default
title : Structures.Congruences module
date : 2021-05-12
author: [the agda-algebras development team][]
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-} -- cubical #-}


module Structures.Congruences where

open import Agda.Builtin.Equality  using    ( _≡_   ;  refl    )
open import Agda.Primitive         using    ( _⊔_   ;  lsuc    )
                                   renaming ( Set   to Type    )
open import Data.Product           using    ( _,_   ;  Σ
                                            ; _×_   ; Σ-syntax )
                                   renaming ( proj₁ to fst     )
open import Function.Base          using    ( _∘_              )
open import Level                  using    ( Level ;  Lift
                                            ; lift  ;  lower   )
                                   renaming ( zero  to ℓ₀      )
open import Relation.Unary         using    ( ∅     ; Pred
                                            ; _∈_              )
open import Relation.Binary        using    ( IsEquivalence    )
                                   renaming ( Rel   to BinRel  )


open import Overture.Preliminaries   using ( ∣_∣ )
open import Structures.Basic         using ( Signature ; Structure
                                           ; _ᵒ_ ; Compatible ; _ʳ_ )
open import Relations.Discrete       using ( _|:_ ; 0[_] )
open import Relations.Quotients      using ( Equivalence ; ⟪_⟫ ; ⌞_⌟
                                           ; 0[_]Equivalence ; _/_
                                           ; ⟪_∼_⟫-elim ; Quotient )
open import Relations.Extensionality using ( swelldef )

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

#### Quotient structures

\begin{code}

 _╱_ : (𝑨 : Structure 𝑅 𝐹 {α}{ρ}) → Con 𝑨 → Structure 𝑅 𝐹 {lsuc (α ⊔ ρ)}{ρ}

 𝑨 ╱ θ = (Quotient (∣ 𝑨 ∣) {α ⊔ ρ} ∣ θ ∣)        -- domain of quotient structure
          , (λ r x → (r ʳ 𝑨) λ i → ⌞ x i ⌟)      -- interpretation of relations
          , λ f b → ⟪ (f ᵒ 𝑨) (λ i → ⌞ b i ⌟)  ⟫ -- interp of operations

 /≡-elim : {𝑨 : Structure 𝑅 𝐹 {α}{ρ}}( (θ , _ ) : Con 𝑨){u v : ∣ 𝑨 ∣}
  →    ⟪ u ⟫{∣ θ ∣} ≡ ⟪ v ⟫ → ∣ θ ∣ u v
 /≡-elim θ {u}{v} x =  ⟪ u ∼ v ⟫-elim {R = ∣ θ ∣} x

\end{code}

Example. The zero congruence of an arbitrary structure.

\begin{code}

 𝟘[_╱_] : (𝑨 : Structure 𝑅 𝐹 {α}{ρ})(θ : Con 𝑨) → BinRel (∣ 𝑨 ∣ / (fst ∣ θ ∣)) (lsuc (α ⊔ ρ))
 𝟘[ 𝑨 ╱ θ ] = λ u v → u ≡ v

𝟎[_╱_] : {α ρ : Level}(𝑨 : Structure 𝑅 𝐹 {α}{ρ})(θ : Con 𝑨) → swelldef ℓ₀ (lsuc (α ⊔ ρ)) → Con (𝑨 ╱ θ)
𝟎[ 𝑨 ╱ θ ] wd = 0[ ∣ 𝑨 ╱ θ ∣ ]Equivalence , 0[ 𝑨 ╱ θ ]Compatible wd

\end{code}

--------------------------------------

[the agda-algebras development team]: https://github.com/ualib/agda-algebras#the-ualib-agda-algebras-development-team


-------------------------------------------------------------------
--                        THE END                                --
-------------------------------------------------------------------
