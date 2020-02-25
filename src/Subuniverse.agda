--File: Subuniverse.agda
--Author: William DeMeo and Siva Somayyajula
--Date: 20 Feb 2020
--Updated: 23 Feb 2020
--Notes: Based on the file `subuniverse.agda` (10 Jan 2020).

{-# OPTIONS --without-K --exact-split #-}

open import Preliminaries
  using (Level; lsuc; _⊔_; _,_; ∣_∣; ⟦_⟧; Pred; _∈_; _∈∈_;im_⊆_; _⊆_; ⋂; ∃; _≡_)

open import Basic
open import Free using (Term)

module Subuniverse where

module _ {i j k l : Level} {S : Signature i j} where
  data _is-supalgebra-of_ (A : Algebra k S) : Pred (Algebra (k ⊔ l) S) (lsuc (i ⊔ j ⊔ k ⊔ l)) where
    mem : {P : Pred ∣ A ∣ l} {B : (o : ∣ S ∣) -> Op (⟦ S ⟧ o) (∃ P)} →
      ((o : ∣ S ∣) → (x : ⟦ S ⟧ o → ∃ P) →
        ∣ B o x ∣ ≡ ⟦ A ⟧ o (λ i → ∣ x i ∣)) →
      A is-supalgebra-of (∃ P , B)

  _is-subalgebra-of_ : Algebra _ S → Algebra _ S → Set _
  B is-subalgebra-of A = A is-supalgebra-of B

private
  variable
    i j k l : Level
    S : Signature i j
    𝑨 : Algebra k S

IsSubuniverse : {S : Signature i j} {𝑨 : Algebra k S}
              ---------------------------------------
              → Pred (Pred ∣ 𝑨 ∣ l) (i ⊔ j ⊔ k ⊔ l)
IsSubuniverse {S = (𝐹 , ρ)} {𝑨 = (A , 𝐹ᴬ)} B =        -- type \MiF\^A for 𝐹ᴬ
  (𝓸 : 𝐹) (𝒂 : ρ 𝓸 → A) → im 𝒂 ⊆ B → 𝐹ᴬ 𝓸 𝒂 ∈ B

module _ {i j k : Level} {S : Signature i j} where

  record Subuniverse  {𝑨 : Algebra k S} : Set (i ⊔ j ⊔ lsuc k) where
    constructor mksub
    field
      sset : Pred ∣ 𝑨 ∣ k
      isSub : IsSubuniverse {𝑨 = 𝑨} sset    

module _ {i j k l : Level} {S : Signature i j} {𝑨 : Algebra k S} where
  data Sg (X : Pred ∣ 𝑨 ∣ l) : Pred ∣ 𝑨 ∣ (i ⊔ j ⊔ k ⊔ l) where
    var : ∀ {v} → v ∈ X → v ∈ Sg X
    app :  (𝓸 : ∣ S ∣) {𝒂 : ⟦ S ⟧ 𝓸 -> ∣ 𝑨 ∣ }
      →   im 𝒂 ⊆ Sg X
      ------------------
      → ⟦ 𝑨 ⟧ 𝓸 𝒂 ∈ Sg X

sgIsSub : (X : Pred ∣ 𝑨 ∣ l) → IsSubuniverse {𝑨 = 𝑨} (Sg X)
sgIsSub _ 𝓸 𝒂 α = app 𝓸 α

-- WARNING: if you move X into the scope of sgIsSmallest, you get the following error:
-- "An internal error has occurred. Please report this as a bug.
--  Location of the error: src/full/Agda/TypeChecking/Monad/Context.hs:119"
-- I think it has to do with variable generalization
module _ {X : Pred ∣ 𝑨 ∣ l} where
  sgIsSmallest : {m : Level} {Y : Pred ∣ 𝑨 ∣ m}
    → IsSubuniverse Y
    → X ⊆ Y
    -----------------
    → Sg X ⊆ Y
  -- By induction on x ∈ Sg X, show x ∈ Y
  sgIsSmallest _ X⊆Y (var v∈X) = X⊆Y v∈X
  sgIsSmallest {Y = Y} YIsSub X⊆Y (app 𝓸 {𝒂} im𝒂⊆SgX) = app∈Y where
    -- First, show the args are in Y
    im𝒂⊆Y : im 𝒂 ⊆ Y
    im𝒂⊆Y i = sgIsSmallest YIsSub X⊆Y (im𝒂⊆SgX i)

    -- Since Y is a subuniverse of 𝑨, it contains the application of 𝓸 to said args
    app∈Y : ⟦ 𝑨 ⟧ 𝓸 𝒂 ∈ Y
    app∈Y = YIsSub 𝓸 𝒂 im𝒂⊆Y

-- Same issue here as above
module _ {m : Level} {I : Set l} {A : I → Pred ∣ 𝑨 ∣ m} where
  sub-inter-is-sub : ((i : I) → IsSubuniverse (A i)) → IsSubuniverse (⋂ I A)
  sub-inter-is-sub Ai-is-Sub 𝓸 𝒂 im𝒂⊆⋂A = α where
    α : ⟦ 𝑨 ⟧ 𝓸 𝒂 ∈ ⋂ I A
    -- Suffices to show (i : I) → ⟦ A ⟧ 𝓸 𝒂 ∈ A i
    -- Immediate from A i being a subuniverse
    α i = Ai-is-Sub i 𝓸 𝒂 λ j → im𝒂⊆⋂A j i

-- Term S X ⊆ Image  ∋ 



