--File: Basic.agda
--Author: William DeMeo and Siva Somayyajula
--Date: 20 Feb 2020
--Updated: 21 Feb 2020
--Notes: Based on the file `basic.agda` (24 Dec 2019).
--       Used for 1st half of talk at JMM Special Session (Jan 2020).

{-# OPTIONS --without-K --exact-split #-}

open import Preliminaries
  using (Level; lzero; lsuc;_⊔_; ∃; _,_)

module Basic where

-- Operations and projections
module _ {i j} where
  Op : Set i → Set j → Set (i ⊔ j)
  Op I A = (I → A) → A

  π : {I : Set i} {A : Set j} → I → Op I A
  π i x = x i

-- i is the universe in which the carrier lives
-- j is the universe in which the arities live
Signature : (i j : Level) → Set (lsuc (i ⊔ j))
Signature i j = ∃ λ (F : Set i) → F → Set j

-- k is the universe in which the operational type lives
Algebra : {i j : Level}
          (k : Level)  ->  Signature i j
          -------------------------------
  ->      Set (i ⊔ j ⊔ lsuc k)
Algebra k (𝐹 , ρ) =
  ∃ λ (A : Set k) -> (𝓸 : 𝐹) -> Op (ρ 𝓸) A

-- Siva, what's wrong with the following?

-- data monoid-op {i : Level} : Set i where
--   e : monoid-op
--   · : monoid-op

-- monoid-sig : {i : Level} -> Signature i lzero
-- monoid-sig = monoid-op , λ {e -> 0; · -> 2}

--Can you show me how this simple algebraic structure would be
--codified in the new syntax of Basic.agda.
