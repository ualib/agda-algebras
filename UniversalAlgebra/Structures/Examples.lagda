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
Sig∅ : signature ℓ₀ ℓ₀
Sig∅ = record { symbol = 𝟘 ; arity = λ () }

-- ... one nulary symbol (e.g., pointed sets)
Sig-0 : signature ℓ₀ ℓ₀
Sig-0 = record { symbol = 𝟙 ; arity = λ 𝟎 → 𝟘 }

Sig-1 : signature ℓ₀ ℓ₀ -- ...one unary
Sig-1 = record { symbol = 𝟙 ; arity = λ 𝟎 → 𝟙 }

-- ...one binary symbol (e.g., magmas, semigroups, semilattices)
Sig-2 : signature ℓ₀ ℓ₀
Sig-2 = record { symbol = 𝟙 ; arity = λ 𝟎 → 𝟚 }

-- ...one ternary symbol (e.g., boolean NAE-3-SAT relational structure)
Sig-3 : signature ℓ₀ ℓ₀
Sig-3 = record { symbol = 𝟙 ; arity = λ 𝟎 → 𝟛 }

-- ...one nulary and one binary (e.g., monoids)
Sig-0-1 : signature ℓ₀ ℓ₀
Sig-0-1 = record { symbol = 𝟚 ; arity = λ{ 𝟚.𝟎 → 𝟘 ; 𝟚.𝟏 → 𝟚 } }

-- ...one nulary, one unary, and one binary (e.g., groups)
Sig-0-1-2 : signature ℓ₀ ℓ₀
Sig-0-1-2 = record { symbol = 𝟛 ; arity = λ{ 𝟛.𝟎 → 𝟘 ; 𝟛.𝟏 → 𝟙 ; 𝟛.𝟐 → 𝟚 } }

\end{code}


An example of a (purely) algebraic structure is a 3-element meet semilattice.

\begin{code}

SL : structure {ℓ₀}{ℓ₀}{ℓ₀}{ℓ₀} Sig-2   -- (one binary operation symbol)
               Sig∅    -- (no relation symbols)
               {ℓ₀}{ℓ₀}

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


nae3sat : structure{ℓ₀}{ℓ₀}{ℓ₀}{ℓ₀}  Sig∅    -- (no operation symbols)
                    Sig-3   -- (one ternary relation symbol)

nae3sat = record { carrier = 𝟚
                 ; op = λ ()
                 ; rel = λ _ x → ((x 𝟛.𝟎) , (x 𝟛.𝟏) , (x 𝟛.𝟐)) ∈ NAE3SAT
                 }


\end{code}
