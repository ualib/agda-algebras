--File: Basic.agda
--Author: William DeMeo and Siva Somayyajula
--Date: 20 Feb 2020
--Updated: 21 Feb 2020
--Notes: Based on the file `basic.agda` (24 Dec 2019).
--       Used for 1st half of talk at JMM Special Session (Jan 2020).

{-# OPTIONS --without-K --exact-split #-}

open import Preliminaries
  using (Level; lzero; lsuc;_⊔_; ∃; _,_;⊥;Bool)

module Basic where

-- Operations and projections
module _ {i j} where
  Op : Set i → Set j → Set (i ⊔ j)
  Op I A = (I → A) → A

  π : {I : Set i} {A : Set j} → I → Op I A
  π i x = x i

-- i is the universe in which the operation symbols lives
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

--Example: monoid
--  A monoid signature has two operation symbols, say, `e`
--  and `·`, of arities 0 and 2, of types `(Empty -> A) -> A` and
--  `(Bool -> A) -> A`, resp. The types indicate that `e` is
--  nullary (i.e., takes no args, equivalently, takes args of
--  type `Empty -> A`), while `·` is binary, as indicated by
--  argument type `Bool -> A`.

data monoid-op : Set where
  e : monoid-op
  · : monoid-op

monoid-sig : Signature _ _
monoid-sig = monoid-op , λ { e → ⊥; · → Bool }





