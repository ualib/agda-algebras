---
layout: default
title : "Exercises.Complexity.FiniteCSP module (The Agda Universal Algebra Library)"
date : "2021-07-26"
author: "agda-algebras development team and Libor Barto"
---

All excercises in this module were created by Libor Barto for students at Charles University in Prague. They were formalized in dependent type theory by the [agda-algebras development team][].

### CSP Exercises

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Exercises.Complexity.FiniteCSP  where

open import Agda.Primitive  using ( ) renaming (lzero to ℓ₀ )
open import Data.Product    using ( _,_ ; _×_ )
open import Data.Unit.Base  using () renaming ( tt to 𝟎 )
open import Relation.Unary  using ( Pred ; _∈_ )

-- Imports from agda-algebras --------------------------------------------------------------
open import Base.Overture.Preliminaries         using ( 𝟚 ; 𝟛 )
open import Base.Relations.Continuous           using ( Rel )
open import Base.Structures.Basic               using ( signature ; structure )
open import Examples.Structures.Signatures using ( S∅ ; S001 ; S021)
open import Base.Structures.Homs                using ( hom )
open signature
open structure

\end{code}

Some exercises below refer to the following relations on 𝟚 := \{0, 1\} (where i, j ∈ 𝟚):

\begin{align*}
 Cᵃᵢ    & := \{ i \}                             \\
 Rᵃ    & := \{ (0, 0), (1, 1) \}                 \\
 Nᵃ    & := \{ (0, 1), (1, 0) \}                  \\
 Sᵃ_{ij}  & := 𝟚² - \{ (i , j) \},                    \\
 Hᵃ    & := 𝟚³ - \{ (1, 1, 0) \}                 \\
 Gᵃ₁   & := \{ (0,0,0), (0,1,1), (1,0,1), (1,1,0) \} \\
 Gᵃ₂   & := \{ (0,0,1), (0,1,0), (1,0,0), (1,1,1) \}
\end{align*}


**Exercise 1**. Prove that the definitions of CSP(𝔸) (satisfiability of a list of constraints, homomorphism   problem, truth of primitive positive formulas) are equivalent.


**Exercise 2**. Find a polymomial-time algorithm for CSP(A), where

2.1. 𝑨 = ({0, 1}, Rᵃ) = (𝟚 , \{(0,0), (1, 1)\})
2.2. 𝑨 = ({0, 1}, Rᵃ, C₀ᵃ, C₁ᵃ) = (𝟚 , \{ (0,0) , (1, 1) \} , \{ 0 \} , \{ 1 \})
2.3. 𝑨 = ({0, 1}, S₁₀ᵃ) = (𝟚 , 𝟚³ - \{ (1, 0) \})
2.4. 𝑨 = ({0, 1}, S₁₀ᵃ, C₀ᵃ, C₁ᵃ) = (𝟚 , 𝟚³ - \{ (1, 0) \} , \{ 0 \} , \{ 1 \})
2.5. 𝑨 = ({0, 1}, S₀₁ᵃ, S₁₀ᵃ, C₀ᵃ, C₁ᵃ) = (𝟚 , 𝟚³ - \{ (0, 1) \} , 𝟚³ - \{ (1, 0) \} , \{ 0 \} , \{ 1 \})
2.6. 𝑨 = ({0, 1}, Nᵃ) = (𝟚 , \{ (0, 1) , (1, 0) \})
2.7. 𝑨 = ({0, 1}, Rᵃ, Nᵃ, C₀ᵃ, C₁ᵃ) = (𝟚 , \{ (0,0) , (1, 1) \} , \{ (0, 1) , (1, 0) \} , \{ 0 \} , \{ 1 \})
2.8. 𝑨 = ({0, 1}, Rᵃ, Nᵃ, C₀ᵃ, C₁ᵃ, 𝑆₀₀, S₀₁ᵃ, S₁₀ᵃ, S₁₁ᵃ) = (𝟚 , \{ (0,0) , (1, 1) \} , \{ (0, 1) , (1, 0) \} , \{ 0 \} , \{ 1 \} , 𝟚³ - \{ (0, 0) \} , 𝟚³ - \{ (0, 1) \} , 𝟚³ - \{ (1, 0) \} , 𝟚³ - \{ (1, 1) \})
2.9. 𝑨 = ({0, 1}, all unary and binary relations)



**Solution 2.1**. If 𝑨 = ({0, 1}, Rᵃ) = (𝟚 , \{(0,0), (1, 1)\}), then an instance of (the HOM
formulation of) CSP(𝑨) is a relational structure 𝑩 = (B, Rᵇ⟩, where Rᵇ ⊆ B² and we must decide
whether there exists a homomorphism f : 𝑩 → 𝑨, that is, a map f : B → A (= 𝟚) such that
∀ (b, b'), if (b, b') ∈ Rᵇ, then (f b, f b') ∈ Rᵇ.

Of course, the constant map f ≡ 0 that sends every element of B to 0 (as well as the
constantly-1 map) is such a homomorphism.  Let's prove this formally.

\begin{code}
module solution-2-1 where

 -- The (purely) relational structure with
 -- + 2-element domain,
 -- + one binary relation Rᵃ := \{(0,0), (1, 1)\}

 data Rᵃ : Pred (𝟚 × 𝟚) ℓ₀ where
  r1 : (𝟚.𝟎 , 𝟚.𝟎 ) ∈ Rᵃ
  r2 : (𝟚.𝟏 , 𝟚.𝟏 ) ∈ Rᵃ

 𝑨 : structure S∅    -- (no operation symbols)
               S001  -- (one binary relation symbol)

 𝑨 = record { carrier = 𝟚
            ; op = λ ()
            ; rel = λ _ x → ((x 𝟚.𝟎) , (x 𝟚.𝟏)) ∈ Rᵃ
            }


 -- Claim: Given an arbitrary 𝑩 in the signatures Sig∅ Sig001, we can construct a homomorphism from 𝑩 to 𝑨.
 claim : (𝑩 : structure {ℓ₀}{ℓ₀}{ℓ₀}{ℓ₀} S∅ S001 {ℓ₀}{ℓ₀}) → hom 𝑩 𝑨
 claim 𝑩 = (λ x → 𝟚.𝟎) , (λ _ _ _ → r1) , λ ()

\end{code}

In general, whenever the template structure 𝑨 has a one-element subuniverse, say, \{ a \},
then the constant map that always gives a is a homomorphism from any structure in the given
signature to 𝑨. ∎



**Solution 2.2**. If 𝑨 = (\{ 0, 1 \}, Rᵃ, C₀ᵃ, C₁ᵃ) = (𝟚 , \{ (0, 0) , (1, 1) \} , \{ 0 \} , \{ 1 \}),
then an instance of HOM CSP(𝑨) is a relational structure 𝑩 = (B, Rᵇ, C₀ᵇ, C₁ᵇ), where
Rᵇ ⊆ B², C₀ᵇ ⊆ B, C₁ᵇ ⊆ B, and we must decide whether there exists a homomorphism
f : hom 𝑩 𝑨, that is, a map f : B → 𝟚 such that the following conditions hold:
 1. ∀ (x, y) ∈ B², (x, y) ∈ Rᵇ implies (f x , f y) ∈ Rᵇ,
 2. f is constantly 0 on C₀ᵇ, and
 3. f is constantly 1 on C₁ᵇ.

The first condition says that if (x, y) ∈ Rᵇ, then either f x = 0 = f y or f x = 1 = f y.

Therefore, there exists a homomorphism f : hom 𝑩 𝑨 iff Rᵇ ∩ C₀ᵇ × C₁ᵇ = ∅ = Rᵇ ∩ C₁ᵇ × C₀ᵇ.

We can check this in polynomial time (in the size of the input instance 𝑩) since we just need
to check each pair (x, y) ∈ Rᵇ and make sure that the following two implications hold:

 1.  x ∈ C₀ᵇ  only if  y ∉ C₁ᵇ, and
 2.  x ∈ C₁ᵇ  only if  y ∉ C₀ᵇ.

\begin{code}

module solution-2-2 where

 -- The (purely) relational structure with
 -- + 2-element domain,
 -- + one binary relation: Rᵃ := { (0,0), (1, 1) }
 -- + two unary relations: C₀ᵃ := { 0 } , C₁ᵃ := { 1 }

 data Rᵃ : Pred (𝟚 × 𝟚) ℓ₀ where
  r1 : (𝟚.𝟎 , 𝟚.𝟎 ) ∈ Rᵃ
  r2 : (𝟚.𝟏 , 𝟚.𝟏 ) ∈ Rᵃ

 data C₀ᵃ : Pred 𝟚 ℓ₀ where
  c₀ : 𝟚.𝟎 ∈ C₀ᵃ

 data C₁ᵃ : Pred 𝟚 ℓ₀ where
  c₁ : 𝟚.𝟏 ∈ C₁ᵃ


 𝑨 : structure S∅    -- (no operations)
               S021  -- (two unary relations and one binary relation)

 𝑨 = record { carrier = 𝟚
            ; op = λ ()
            ; rel = rels
            }
            where
            rels : (r : 𝟛) → Rel 𝟚 (arity S021 r)
            rels 𝟛.𝟎 x = ((x 𝟚.𝟎) , (x 𝟚.𝟏)) ∈ Rᵃ
            rels 𝟛.𝟏 x = x 𝟎 ∈ C₀ᵃ
            rels 𝟛.𝟐 x = x 𝟎 ∈ C₁ᵃ


 -- Claim: Given an arbitrary 𝑩 in the signatures S∅ S021, we can construct a homomorphism from 𝑩 to 𝑨.
 -- claim :  (𝑩 : structure S∅ S021 {ℓ₀}{ℓ₀})
 --  →       (∀ (x : 𝟚 → carrier 𝑩)
 --           → (rel 𝑩) 𝟛.𝟎 x  -- if ((x 𝟚.𝟎) , (x 𝟚.𝟏)) ∈ Rᵇ, then...
 --           → ((rel 𝑩) 𝟛.𝟏 (λ _ → (x 𝟚.𝟎)) → ¬ (rel 𝑩) 𝟛.𝟐 (λ _ → (x 𝟚.𝟏)))
 --             × ((rel 𝑩) 𝟛.𝟏 (λ _ → (x 𝟚.𝟏)) → ¬ (rel 𝑩) 𝟛.𝟐 (λ _ → (x 𝟚.𝟎)))
 --          --  × (x 𝟚.𝟎 ∈ C₁ᵇ → x 𝟚.𝟏 ∉ C₀ᵇ))
 --          )
 --  →       hom 𝑩 𝑨
 -- claim 𝑩 x = {!!}

\end{code}


(The remainder are "todo.")

**Solution 2.3**. 𝑨 = ({0, 1}, S₁₀ᵃ) = (𝟚 , 𝟚³ - \{ (1, 0) \})

**Solution 2.4**. 𝑨 = ({0, 1}, S₁₀ᵃ, C₀ᵃ, C₁ᵃ) = (𝟚 , 𝟚³ - \{ (1, 0) \} , \{ 0 \} , \{ 1 \})

**Solution 2.5**. 𝑨 = ({0, 1}, S₀₁ᵃ, S₁₀ᵃ, C₀ᵃ, C₁ᵃ) = (𝟚 , 𝟚³ - \{ (0, 1) \} , 𝟚³ - \{ (1, 0) \} , \{ 0 \} , \{ 1 \})

**Solution 2.6**. 𝑨 = ({0, 1}, Nᵃ) = (𝟚 , \{ (0, 1) , (1, 0) \})

**Solution 2.7**. 𝑨 = ({0, 1}, Rᵃ, Nᵃ, C₀ᵃ, C₁ᵃ) = (𝟚 , \{ (0,0) , (1, 1) \} , \{ (0, 1) , (1, 0) \} , \{ 0 \} , \{ 1 \})

**Solution 2.8**. 𝑨 = ({0, 1}, Rᵃ, Nᵃ, C₀ᵃ, C₁ᵃ, 𝑆₀₀, S₀₁ᵃ, S₁₀ᵃ, S₁₁ᵃ) = (𝟚 , \{ (0,0) , (1, 1) \} , \{ (0, 1) , (1, 0) \} , \{ 0 \} , \{ 1 \} , 𝟚³ - \{ (0, 0) \} , 𝟚³ - \{ (0, 1) \} , 𝟚³ - \{ (1, 0) \} , 𝟚³ - \{ (1, 1) \})

**Solution 2.9**. 𝑨 = ({0, 1}, all unary and binary relations)


**Exercise 3**. Find a polynomial-time algorithm for CSP({0, 1}, Hᵃ, C₀ᵃ, C₁ᵃ).

**Exercise 4**. Find a polynomial-time algorithm for CSP({0, 1}, C₀ᵃ, C₁ᵃ, G₁ᵃ, G₂ᵃ).

**Exercise 5**. Find a polynomial-time algorithm for CSP(ℚ, <).

--------------------------------

{% include UALib.Links.md %}


