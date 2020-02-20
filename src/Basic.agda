open import Preliminaries using (Level; suc; _⊔_; ∃; _,_)

module Basic where

-- Operations and projections
module _ {i j} where
  Op : Set i → Set j → Set (i ⊔ j)
  Op I A = (I → A) → A

  π : {I : Set i} {A : Set j} → I → Op I A
  π i x = x i

-- i is the universe in which the carrier lives
-- j is the universe in which the arities live
Signature : (i j : Level) → Set (suc (i ⊔ j))
Signature i j = ∃ λ (F : Set i) → F → Set j

-- k is the universe in which the operational type lives
Algebra : {i j : Level} (k : Level) → Signature i j → Set (i ⊔ j ⊔ suc k)
Algebra k (F , ρ) = ∃ λ (A : Set k) → (o : F) → Op (ρ o) A
