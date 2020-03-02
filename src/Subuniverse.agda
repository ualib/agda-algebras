--File: Subuniverse.agda
--Author: William DeMeo and Siva Somayyajula
--Date: 20 Feb 2020
--Up6 
--Notes: Based on the file `subuniverse.agda` (10 Jan 2020).

{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

open import Preliminaries
open import Basic
open import Free

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

module _ {i j k : Level} {S : Signature i j} where
  -- To keep A at same universe level as ∃ P , B, force P to live in the same universe
  -- We need to do this so that both A and ∃ P , B can be classified by the same predicate SClo
  data _is-supalgebra-of_ (𝑨 : Algebra k S) : Pred (Algebra k S) (lsuc (i ⊔ j ⊔ k)) where
    mem : {P : Pred ∣ 𝑨 ∣ k} {B : (𝓸 : ∣ S ∣) -> Op (⟦ S ⟧ 𝓸) (∃ P)} →
            ((𝓸 : ∣ S ∣) → (x : ⟦ S ⟧ 𝓸 → ∃ P) → ∣ B 𝓸 x ∣ ≡ ⟦ 𝑨 ⟧ 𝓸 (λ i → ∣ x i ∣)) →
          𝑨 is-supalgebra-of (∃ P , B)

  _is-subalgebra-of_ : Algebra _ S → Algebra _ S → Set _
  B is-subalgebra-of A = A is-supalgebra-of B

module _ {S : Signature i j} {𝑨 : Algebra k S} {B : Pred ∣ 𝑨 ∣ k} (P : B ∈ Subuniverses 𝑨) where
  SubunivAlg : Algebra k S
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

module _ {S : Signature i j} {𝑨 𝑩 : Algebra k S} (f : Hom 𝑨 𝑩) where
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

module _  {S : Signature i j} {𝑨 𝑩 : Algebra k S} {B : Pred ∣ 𝑨 ∣ l} (X Y : Set k) where

  -- Subuniverses are closed under the action of term operations.
  sub-term-closed : B ∈ Subuniverses 𝑨
    ->              (𝒕 : Term)
    ->              (𝒃 : X -> ∣ 𝑨 ∣)
    ->              (∀ i -> 𝒃 i ∈ B)
                 -------------------------
    ->              ((𝒕 ̇ 𝑨) 𝒃) ∈ B
  sub-term-closed B≤𝑨 (generator x) 𝒃 𝒃∈B = 𝒃∈B x
  sub-term-closed B≤𝑨 (node 𝓸 𝒕) 𝒃 𝒃∈B =
    B≤𝑨 𝓸 (λ z → (𝒕 z ̇ 𝑨) 𝒃) (λ x → sub-term-closed B≤𝑨 (𝒕 x) 𝒃 𝒃∈B)
    -- AUTOMATION WORKS! (this proof was found automatically by C-c C-a)

  -- Obs 2.11 (on subuniverse generation as image of terms) (cf. UAFST Thm 4.32(3))
  -- If Y is a subset of A, then
  --    Sg(Y) = {t(a₁,...,aₙ) : t ∈ T(Xₙ), n < ω, aᵢ ∈ Y, i ≤ n}.
  -- Or, in our notation, 
  --   Sg^{𝑨}(Y) = { 𝒕^𝑨 𝒂 : 𝒕 ∈ Term{X}, 𝒂 : X -> Y }.
  -- Paper-pencil-proof.
  --   Induction on the height of t shows that every subuniverse is closed
  --   under the action of t^𝑨. Thus the right-hand side (RHS) is contained
  --   in the left. The formalization is given by `sub-term-closed`; it proves
  --      Sg^{𝑨}(Y) ⊇ { 𝒕^𝑨 𝒂 : 𝒕 ∈ Term{X}, 𝒂 : X -> Y }.
  --   On the other hand, the RHS is a subuniverse that contains Y (take t = x₁), so
  --   contains Sg^{𝑨}(Y), as the latter is the smallest subuniverse containing Y. ☐
  --   So, we prove Sg^{𝑨}(Y) ⊆ { 𝒕^𝑨 𝒂 : 𝒕 ∈ Term{X}, 𝒂 : X -> Y } following these steps:
  -- 1. The image of Y under all terms, `TermImage Y`, is a subuniverse of 𝑨.
  --    That is, TermImageY = ⋃{𝒕:Term} Image (𝒕 ̇ 𝑨) ≤ 𝑨.
  -- 2. Y ⊆ TermImageY (obvious)
  -- 3. Sg^𝑨(Y) is the smallest subuniverse containing Y (see `sgIsSmallest`)
  --    so Sg^𝑨(Y) ⊆ TermImageY ∎
  TermImage : Pred ∣ 𝑨 ∣ (i ⊔ j ⊔ k) -> Pred ∣ 𝑨 ∣ (i ⊔ j ⊔ k)
  TermImage Y = λ (a : ∣ 𝑨 ∣ )
     --    ->          ∃ λ (ta : Term × ( X -> ∣ 𝑨 ∣ ) )
    ->          ∃ λ (𝒕 : Term)
    ->          a ≡ evalt 𝒕
      where
        evalt : ∣ 𝑨 ∣ -> Term -> ∣ 𝑨 ∣
        evalt a (generator x) = a  -- ∃ λ (arg : X -> ∣ 𝑨 ∣ ) -> (a ≡ arg x)
        evalt a (node 𝓸 𝒕) = ∃ λ (args : ⟦ S ⟧ 𝓸 -> X -> ∣ 𝑨 ∣ ) -> (a ≡ (⟦ 𝑨 ⟧ 𝓸) ((λ i -> (𝒕 i) ̇ 𝑨) Fork args))

  TermHelper : {𝓸 : ∣ S ∣} -> Pred ∣ 𝑨 ∣ (i ⊔ j ⊔ k) -> Pred (⟦ S ⟧ 𝓸 -> ∣ 𝑨 ∣ ) (i ⊔ j ⊔ k)
  TermHelper {𝓸} Y = λ (𝒂 : ⟦ S ⟧ 𝓸 -> ∣ 𝑨 ∣ )
    ->          ∃ λ (𝒕𝒂 :  ⟦ S ⟧ 𝓸 -> Term )
    ->          ∃ λ (args :  ⟦ S ⟧ 𝓸 -> ( X -> ∣ 𝑨 ∣ ) )
    ->          ∀ i -> (∀ x -> (args i) x ∈ Y)
              -----------------------------
    ->           𝒂 i ≡ ( (𝒕𝒂 i)  ̇ 𝑨) (args i)


  TermHelper2 : {𝓸 : ∣ S ∣} -> (Y : Pred ∣ 𝑨 ∣ (i ⊔ j ⊔ k))
    ->               (𝒂 : ⟦ S ⟧ 𝓸 -> ∣ 𝑨 ∣ )
    ->               (𝒂 ∈ TermHelper Y)
                   ----------------------------------------
    ->               (∀ i -> (𝒂 i) ∈ TermImage Y)
  TermHelper2 {𝓸} Y 𝒂 TIH = λ i₁ ->
     (∣ TIH ∣ i₁ ,  ∣ ⟦ TIH ⟧ ∣ i₁) , λ x ->  ⟦ ⟦ TIH ⟧ ⟧ i₁ x

  TermHelper3 : {𝓸 : ∣ S ∣} -> (Y : Pred ∣ 𝑨 ∣ (i ⊔ j ⊔ k))
    ->               (𝒂 : ⟦ S ⟧ 𝓸 -> ∣ 𝑨 ∣ )
    ->               (𝒂 ∈ TermHelper Y)
                   ----------------------------------------
    ->               ⟦ 𝑨 ⟧ 𝓸 𝒂 ∈ TermImage Y
  TermHelper3 {𝓸} Y 𝒂 TIH =
    let TH2 = TermHelper2 Y 𝒂 TIH in {!!} , {!!}
    -- (node 𝓸 (λ i -> ∣ ∣ TH2 i ∣ ∣ ) , ⟦ ∣ TH2 _ ∣ ⟧) , λ x → cong ( ⟦ 𝑨 ⟧ 𝓸 )  ((∀-extensionality-ℓ₁-ℓ₂) λ x₁ → refl)
    -- (node 𝓸 (λ a -> ∣ TIH ∣ Fork a) , {!!}) , {!!}

-- We have, for each 𝒂 i, a term 𝒕 : i -> term and
-- args : i -> (X -> ∣ 𝑨 ∣ ) such that 𝒂 i = (𝒕 i) (args i).
-- But we need to combine these terms (easy: node 𝓸 𝒕)
-- AND the arguments so that args : X -> ∣ 𝑨 ∣.
  
  --1. TermImage is a subuniverse
  TermImageSub : (Y : Pred ∣ 𝑨 ∣ (i ⊔ j ⊔ k))
                -------------------------------
    ->           TermImage Y ∈ Subuniverses 𝑨
  TermImageSub Y 𝓸 𝒂 ta =
    let tt = λ x₁ -> ∣ ∣ ta x₁ ∣ ∣ in 
    let ttA = λ x₁ -> (∣ ∣ ta x₁ ∣ ∣ ̇ 𝑨) in 
    let Args = λ x₁ -> ⟦ ∣ ta x₁ ∣ ⟧ in
    let pf = λ x₁ -> ⟦ ta x₁ ⟧ in 
    let TFA = ttA Fork Args in
    let 𝒂' = ⟦ 𝑨 ⟧ 𝓸 Eval TFA in
    let fin = ⟦ 𝑨 ⟧ 𝓸 𝒂 ≡ 𝒂' in ( node 𝓸 tt ,  {!!} ) , λ x → cong (⟦ 𝑨 ⟧ 𝓸) {!!}


  -- We must show TY := { 𝒕^𝑨 𝒂 : 𝒕 ∈ Term{X}, 𝒂 : X -> Y } is a subalgebra.
  -- That is,  ∀ 𝓸 : ∣ S ∣, if args : ⟦ S ⟧ 𝓸 -> TY, then ⟦ 𝑨 ⟧ 𝓸 args ∈ TY.
  -- args : ⟦ S ⟧ 𝓸 -> TY means, ∀ i -> ∃ ∣ taᵢ ∣ : Term × ( X -> ∣ 𝑨 ∣ )
  --   ->   (∀ x -> ⟦ ∣ taᵢ ∣ ⟧ x ∈ Y)  ->  args i ≡ (∣ ∣ taᵢ ∣ ∣ ̇ 𝑨) ⟦ ∣ taᵢ ∣ ⟧
  -- It follows that 
  --   ⟦ 𝑨 ⟧ 𝓸 args ≡ ⟦ 𝑨 ⟧ 𝓸 (λ i -> args i) ≡ ⟦ 𝑨 ⟧ 𝓸 (λ i -> (∣ ∣ taᵢ ∣ ∣ ̇ 𝑨) ⟦ ∣ taᵢ ∣ ⟧)
  -- Remains to show ∃ TA such that ∣ ∣ TA ∣ ∣ : Term and ⟦ ∣ TA ∣ ⟧ : X -> ∣ 𝑨 ∣ satisfy:
  --   ⟦ 𝑨 ⟧ 𝓸 args ≡ ⟦ 𝑨 ⟧ 𝓸 (∣ ∣ TA ∣ ∣ ̇ 𝑨) ⟦ ∣ TA ∣ ⟧
  -- 
  -- Since args : ⟦ S ⟧ 𝓸 -> TY and ∀ i -> ∣ ∣ taᵢ ∣ ∣ , ⟦ ∣ taᵢ ∣ ⟧ satisfy
  --    args i ≡ (∣ ∣ taᵢ ∣ ∣ ̇ 𝑨) ⟦ ∣ taᵢ ∣ ⟧,
  -- we have, by ∀-extensionality, args ≡ λ i -> (∣ ∣ taᵢ ∣ ∣ ̇ 𝑨) ⟦ ∣ taᵢ ∣ ⟧
  -- Then, by cong (⟦ 𝑨 ⟧ 𝓸) we have the desired equivalence:
  -- ⟦ 𝑨 ⟧ 𝓸 args ≡ ⟦ 𝑨 ⟧ 𝓸 (λ i -> (∣ ∣ taᵢ ∣ ∣ ̇ 𝑨) ⟦ ∣ taᵢ ∣ ⟧)
  --
 
  --2. Y ⊆ TermImageY
  Y⊆TermImageY : {x : X} -> (Y : Pred ∣ 𝑨 ∣ (i ⊔ j ⊔ k)) -> Y ⊆ TermImage Y
  Y⊆TermImageY {x} Y {a} a∈Y = ( generator x , (λ x -> a) ) , λ x₁ → refl
  
  -- 3. Sg^𝑨(Y) is the smallest subuniverse containing Y
  --    Proof: see `sgIsSmallest`

  --Finally, we can prove the desired inclusion.
  SgY⊆TermImageY : {x : X} -> (Y : Pred ∣ 𝑨 ∣ (i ⊔ j ⊔ k)) -> Sg Y ⊆ TermImage Y
  SgY⊆TermImageY {x} Y = sgIsSmallest (TermImageSub Y) (Y⊆TermImageY{x} Y)

  -- We should now be able to prove the following (if we wanted to):
  -- SgY≃TermImageY : {x : X} -> (Y : Pred ∣ 𝑨 ∣ (i ⊔ j ⊔ k)) -> (Sg Y) ≃ (TermImage Y)
  -- SgY≃TermImageY {x} Y = ? 
