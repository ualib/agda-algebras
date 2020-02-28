--File: Subuniverse.agda
--Author: William DeMeo and Siva Somayyajula
--Date: 20 Feb 2020
--Updated: 26 Feb 2020
--Notes: Based on the file `subuniverse.agda` (10 Jan 2020).

{-# OPTIONS --without-K --exact-split #-}

open import Preliminaries
--  using (Level; lsuc; _⊔_; _,_; ∣_∣; ⟦_⟧; Pred; _∈_; _∈∈_;Im_⊆_; _⊆_; ⋂; ∃; _≡_; Image; _∘_; refl;Inv)
-- proj₁;proj₂; 
open import Basic
open import Free using (Term)

module Subuniverse where

private
  variable
    i j k l : Level
    S : Signature i j
    𝑨 : Algebra k S
    𝑩 : Algebra l S

Subuniverses : {S : Signature i j} → (𝑨 : Algebra k S) →
              ---------------------------------------
               Pred (Pred ∣ 𝑨 ∣ l) (i ⊔ j ⊔ k ⊔ l)
Subuniverses {S = 𝐹 , ρ} (A , 𝐹ᴬ) a =        -- type \MiF\^A for 𝐹ᴬ
  (𝓸 : 𝐹) (𝒂 : ρ 𝓸 → A) → Im 𝒂 ⊆ a → 𝐹ᴬ 𝓸 𝒂 ∈ a

module _ {S : Signature i j} {𝑨 : Algebra k S} {B : Pred ∣ 𝑨 ∣ l} (P : B ∈ Subuniverses 𝑨) where
  SubunivAlg : Algebra (k ⊔ l) S
  SubunivAlg = ∃ B , λ 𝓸 x → ⟦ 𝑨 ⟧ 𝓸 (∣_∣ ∘ x) , P 𝓸 (∣_∣ ∘ x) (⟦_⟧ ∘ x)
  --  SubunivAlg = ∃ B , λ 𝓸 x → ⟦ 𝑨 ⟧ 𝓸 (proj₁ ∘ x) , P 𝓸 (proj₁ ∘ x) (proj₂ ∘ x)

  subuniv-to-subalg : SubunivAlg is-subalgebra-of 𝑨
  subuniv-to-subalg = mem λ _ _ → refl

module _ {i j k : Level} {S : Signature i j} where
  record Subuniverse  {𝑨 : Algebra k S} : Set (i ⊔ j ⊔ lsuc k) where
    constructor mksub
    field
      sset  : Pred ∣ 𝑨 ∣ k
      isSub : sset ∈ Subuniverses 𝑨

module _ {i j k l : Level} {S : Signature i j} {𝑨 : Algebra k S} where
  data Sg (X : Pred ∣ 𝑨 ∣ l) : Pred ∣ 𝑨 ∣ (i ⊔ j ⊔ k ⊔ l) where
    var : ∀ {v} → v ∈ X → v ∈ Sg X
    app :  (𝓸 : ∣ S ∣) {𝒂 : ⟦ S ⟧ 𝓸 -> ∣ 𝑨 ∣ }
      →   Im 𝒂 ⊆ Sg X
      ------------------
      → ⟦ 𝑨 ⟧ 𝓸 𝒂 ∈ Sg X

sgIsSub : (X : Pred ∣ 𝑨 ∣ l) → Sg X ∈ Subuniverses 𝑨
sgIsSub _ 𝓸 𝒂 α = app 𝓸 α

-- WARNING: if you move X into the scope of sgIsSmallest, you get the following error:
-- "An internal error has occurred. Please report this as a bug.
--  Location of the error: src/full/Agda/TypeChecking/Monad/Context.hs:119"
-- I think it has to do with variable generalization
module _ {X : Pred ∣ 𝑨 ∣ l} where
  sgIsSmallest : {m : Level} {Y : Pred ∣ 𝑨 ∣ m}
    → Y ∈ Subuniverses 𝑨
    → X ⊆ Y
    -----------------
    → Sg X ⊆ Y
  -- By induction on x ∈ Sg X, show x ∈ Y
  sgIsSmallest _ X⊆Y (var v∈X) = X⊆Y v∈X
  sgIsSmallest {Y = Y} YIsSub X⊆Y (app 𝓸 {𝒂} im𝒂⊆SgX) = app∈Y where
    -- First, show the args are in Y
    im𝒂⊆Y : Im 𝒂 ⊆ Y
    im𝒂⊆Y i = sgIsSmallest YIsSub X⊆Y (im𝒂⊆SgX i)

    -- Since Y is a subuniverse of 𝑨, it contains the application of 𝓸 to said args
    app∈Y : ⟦ 𝑨 ⟧ 𝓸 𝒂 ∈ Y
    app∈Y = YIsSub 𝓸 𝒂 im𝒂⊆Y

-- Same issue here as above
-- Obs 2.5. Suppose Aᵢ ≤ 𝑨 for all i in some set I. Then ⋂ᵢ Aᵢ is a subuniverse of 𝑨.
module _ {m : Level} {I : Set l} {A : I → Pred ∣ 𝑨 ∣ m} where
  sub-inter-is-sub : ((i : I) → A i ∈ Subuniverses 𝑨) → ⋂ I A ∈ Subuniverses 𝑨
  sub-inter-is-sub Ai-is-Sub 𝓸 𝒂 im𝒂⊆⋂A = α where
    α : ⟦ 𝑨 ⟧ 𝓸 𝒂 ∈ ⋂ I A
    -- Suffices to show (i : I) → ⟦ A ⟧ 𝓸 𝒂 ∈ A i
    -- Immediate from A i being a subuniverse
    α i = Ai-is-Sub i 𝓸 𝒂 λ j → im𝒂⊆⋂A j i

-- Hom is subuniverse

open import Hom

module _ {S : Signature i j} {𝑨 𝑩 : Algebra k S} {B : Pred ∣ 𝑨 ∣ l} (f : Hom 𝑨 𝑩) where
  HomImage : ∣ 𝑩 ∣ -> Set k
  HomImage = λ b -> Image ∣ f ∣ ∋ b

  hom-image-is-sub : HomImage ∈ Subuniverses 𝑩
  hom-image-is-sub 𝓸 𝒃 𝒃∈Imf = 
    let 𝒂 = λ x -> Inv ∣ f ∣ (𝒃 x) (𝒃∈Imf x) in
    let 𝒃≡𝒄 = ∀-extensionality-ℓ₁-ℓ₂
              (λ x -> InvIsInv ∣ f ∣ (𝒃 x) (𝒃∈Imf x)) in 
    let fin = trans (⟦ f ⟧ 𝓸 𝒂) (cong ( ⟦ 𝑩 ⟧ 𝓸 ) 𝒃≡𝒄) in
      eq (⟦ 𝑩 ⟧ 𝓸 (λ x → 𝒃 x)) ( ⟦ 𝑨 ⟧ 𝓸 𝒂) (sym fin)

-- Paper-pencil-proof.
-- Let 𝓸 be an op symbol.  Let args : ⟦ S ⟧ 𝓸 -> ∣ 𝑩 ∣ be a (⟦ S ⟧ 𝓸)-tuple of elements ∣ 𝑩 ∣.
-- Assume ∀ i₁ -> args i₁ ∈ Image ∣ f ∣.
-- We must show (⟦ 𝑩 ⟧ 𝓸) args ∈ Image ∣ f ∣.
-- ∀ i₁ -> args i₁ ∈ Image ∣ f ∣ implies
-- ∃ 𝒂 : ⟦ S ⟧ 𝓸 -> ∣ 𝑨 ∣ such that ∣ f ∣ ∘ 𝒂 = args.
-- i.e., ∀ i₁ ->  ∣ f ∣ 𝒂 i₁ = args i₁.
-- Sine f : Hom 𝑨 𝑩, we have
-- (⟦ 𝑩 ⟧ 𝓸) args = (⟦ 𝑩 ⟧ 𝓸) (∣ f ∣ ∘ 𝒂) = ∣ f ∣ ⟦ 𝑨 ⟧ 𝓸 𝒂 ∈ Image ∣ f ∣ 


{-
-- Problem is, don't think you can convert this to an equational definition
-- since it's not well-founded
data H {i j k l} {S : Signature i j} (K : Pred (Algebra k S) l) : Pred (Algebra k S) {!!} where
  hbase : {A : Algebra k S} → A ∈ K → A ∈ H K
  hhom : {A B : Algebra k S} {f : Hom A B} → A ∈ K → B ∈ K →
    SubunivAlg (hom-image-is-sub f) ∈ H K
-}

