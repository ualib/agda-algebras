---
layout: default
title : Structures.Examples module (Agda Universal Algebra Library)
date : 2021-07-16
author: [agda-algebras development team][]
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Structures.Examples where

open import Agda.Primitive  using ( Level ) renaming ( Set to Type ; lzero to ℓ₀ )
open import Data.Product    using ( _,_ ; _×_  )
open import Relation.Unary  using ( Pred ; _∈_ ; ⋂ )

open import Overture.Preliminaries using ( 𝟘 ; 𝟙 ; 𝟚 ; 𝟛 )
open import Structures.Basic       using ( signature ; structure )



-- Some examples (of finite signatures)
-- The signature with...
-- ... no symbols  (e.g., sets)
S∅ : signature ℓ₀ ℓ₀
S∅ = record { symbol = 𝟘 ; arity = λ () }

-- ... one nullary symbol (e.g., pointed sets)
S1 : signature ℓ₀ ℓ₀
S1 = record { symbol = 𝟙 ; arity = λ 𝟎 → 𝟘 }

S01 : signature ℓ₀ ℓ₀ -- ...one unary
S01 = record { symbol = 𝟙 ; arity = λ 𝟎 → 𝟙 }

-- ...one binary symbol (e.g., magmas, semigroups, semilattices)
S001 : signature ℓ₀ ℓ₀
S001 = record { symbol = 𝟙 ; arity = λ 𝟎 → 𝟚 }

-- ...one ternary symbol (e.g., boolean NAE-3-SAT relational structure)
S0001 : signature ℓ₀ ℓ₀
S0001 = record { symbol = 𝟙 ; arity = λ 𝟎 → 𝟛 }

-- ...0 nullary, 2 unary, and 1 binary
S021 : signature ℓ₀ ℓ₀
S021 = record { symbol = 𝟛 ; arity = λ{ 𝟛.𝟎 → 𝟚 ; 𝟛.𝟏 → 𝟙 ; 𝟛.𝟐 → 𝟙 } }

-- ...one nullary and one binary (e.g., monoids)
S101 : signature ℓ₀ ℓ₀
S101 = record { symbol = 𝟚 ; arity = λ{ 𝟚.𝟎 → 𝟘 ; 𝟚.𝟏 → 𝟚 } }

-- ...one nullary, one unary, and one binary (e.g., groups)
S111 : signature ℓ₀ ℓ₀
S111 = record { symbol = 𝟛 ; arity = λ{ 𝟛.𝟎 → 𝟘 ; 𝟛.𝟏 → 𝟙 ; 𝟛.𝟐 → 𝟚 } }

\end{code}


An example of a (purely) algebraic structure is a 3-element meet semilattice.

\begin{code}

SL : structure S001   -- (one binary operation symbol)
               S∅     -- (no relation symbols)
               {ρ = ℓ₀}

SL = record { carrier = 𝟛
            ; op = λ _ x → meet (x 𝟚.𝟎) (x 𝟚.𝟏)
            ; rel = λ ()
            } where
              meet : 𝟛 → 𝟛 → 𝟛
              meet 𝟛.𝟎 𝟛.𝟎 = 𝟛.𝟎
              meet 𝟛.𝟎 𝟛.𝟏 = 𝟛.𝟎
              meet 𝟛.𝟎 𝟛.𝟐 = 𝟛.𝟎
              meet 𝟛.𝟏 𝟛.𝟎 = 𝟛.𝟎
              meet 𝟛.𝟏 𝟛.𝟏 = 𝟛.𝟏
              meet 𝟛.𝟏 𝟛.𝟐 = 𝟛.𝟎
              meet 𝟛.𝟐 𝟛.𝟎 = 𝟛.𝟎
              meet 𝟛.𝟐 𝟛.𝟏 = 𝟛.𝟎
              meet 𝟛.𝟐 𝟛.𝟐 = 𝟛.𝟐

\end{code}

An example of a (purely) relational structure is the 2 element structure with
the ternary NAE-3-SAT relation, R = S³ - {(0,0,0), (1,1,1)} (where S = {0, 1}).

\begin{code}

data NAE3SAT : Pred (𝟚 × 𝟚 × 𝟚) ℓ₀ where
 r1 : (𝟚.𝟎 , 𝟚.𝟎 , 𝟚.𝟏) ∈ NAE3SAT
 r2 : (𝟚.𝟎 , 𝟚.𝟏 , 𝟚.𝟎) ∈ NAE3SAT
 r3 : (𝟚.𝟎 , 𝟚.𝟏 , 𝟚.𝟏) ∈ NAE3SAT
 r4 : (𝟚.𝟏 , 𝟚.𝟎 , 𝟚.𝟎) ∈ NAE3SAT
 r5 : (𝟚.𝟏 , 𝟚.𝟎 , 𝟚.𝟏) ∈ NAE3SAT
 r6 : (𝟚.𝟏 , 𝟚.𝟏 , 𝟚.𝟎) ∈ NAE3SAT


nae3sat : structure S∅    -- (no operation symbols)
                    S0001 -- (one ternary relation symbol)

nae3sat = record { carrier = 𝟚
                 ; op = λ ()
                 ; rel = λ _ x → ((x 𝟛.𝟎) , (x 𝟛.𝟏) , (x 𝟛.𝟐)) ∈ NAE3SAT
                 }


\end{code}
